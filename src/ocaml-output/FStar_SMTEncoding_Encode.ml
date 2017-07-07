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
             FStar_Syntax_Syntax.pos = uu____2378;
             FStar_Syntax_Syntax.vars = uu____2379;_},uu____2380)
          ->
          let uu____2395 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2395 FStar_Option.isNone
      | uu____2404 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2413 =
        let uu____2414 = FStar_Syntax_Util.un_uinst t in
        uu____2414.FStar_Syntax_Syntax.n in
      match uu____2413 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2417,uu____2418,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_2432  ->
                  match uu___109_2432 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2433 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2435 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2435 FStar_Option.isSome
      | uu____2444 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2453 = head_normal env t in
      if uu____2453
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
    let uu____2467 =
      let uu____2468 = FStar_Syntax_Syntax.null_binder t in [uu____2468] in
    let uu____2469 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____2467 uu____2469 FStar_Pervasives_Native.None
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
                    let uu____2496 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2496
                | s ->
                    let uu____2500 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2500) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___110_2515  ->
    match uu___110_2515 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2516 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____2547;
                       FStar_SMTEncoding_Term.rng = uu____2548;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2562) ->
              let uu____2567 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2584 -> false) args (FStar_List.rev xs)) in
              if uu____2567
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____2587,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2590 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2594 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2594)) in
              if uu____2590
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____2597 -> FStar_Pervasives_Native.None in
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
    | uu____2764 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2768  ->
    match uu___111_2768 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2770 =
          let uu____2774 =
            let uu____2776 =
              let uu____2777 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2777 in
            [uu____2776] in
          ("FStar.Char.Char", uu____2774) in
        FStar_SMTEncoding_Util.mkApp uu____2770
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____2785 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2785
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____2787) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2796) ->
        let uu____2799 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2799
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2803 =
          let uu____2804 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2804 in
        failwith uu____2803
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2825 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2833 ->
            let uu____2838 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2838
        | uu____2839 ->
            if norm1
            then let uu____2840 = whnf env t1 in aux false uu____2840
            else
              (let uu____2842 =
                 let uu____2843 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2844 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2843 uu____2844 in
               failwith uu____2842) in
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
    | uu____2866 ->
        let uu____2867 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2867)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2899::uu____2900::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Parser_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2903::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
  | uu____2905 -> false
let isInteger: FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____2919 -> false
let getInteger: FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____2930 -> failwith "Expected an Integer term"
let is_BitVector_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar
     fv,(sz_arg,uu____2973)::uu____2974::uu____2975::[]) ->
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
          || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_ult_lid))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
        && (isInteger sz_arg.FStar_Syntax_Syntax.n)
  | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3011)::uu____3012::[]) ->
      (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) &&
        (isInteger sz_arg.FStar_Syntax_Syntax.n)
  | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3040)::[]) ->
      ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_zero_vec_lid)
         ||
         (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_ones_vec_lid))
        && (isInteger sz_arg.FStar_Syntax_Syntax.n)
  | uu____3058 -> false
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
        (let uu____3212 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3212
         then
           let uu____3213 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3213
         else ());
        (let uu____3215 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3264  ->
                   fun b  ->
                     match uu____3264 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3307 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____3316 = gen_term_var env1 x in
                           match uu____3316 with
                           | (xxsym,xx,env') ->
                               let uu____3330 =
                                 let uu____3333 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3333 env1 xx in
                               (match uu____3330 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____3307 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____3215 with
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
          let uu____3421 = encode_term t env in
          match uu____3421 with
          | (t1,decls) ->
              let uu____3428 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3428, decls)
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
          let uu____3436 = encode_term t env in
          match uu____3436 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____3445 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3445, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____3447 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3447, decls))
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
        let uu____3453 = encode_args args_e env in
        match uu____3453 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3465 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3472 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3472 in
            let binary arg_tms1 =
              let uu____3481 =
                let uu____3482 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3482 in
              let uu____3483 =
                let uu____3484 =
                  let uu____3485 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3485 in
                FStar_SMTEncoding_Term.unboxInt uu____3484 in
              (uu____3481, uu____3483) in
            let mk_default uu____3490 =
              let uu____3491 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3491 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3532 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3532
              then
                let uu____3533 = let uu____3534 = mk_args ts in op uu____3534 in
                FStar_All.pipe_right uu____3533 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3557 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3557
              then
                let uu____3558 = binary ts in
                match uu____3558 with
                | (t1,t2) ->
                    let uu____3563 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3563
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3566 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3566
                 then
                   let uu____3567 = op (binary ts) in
                   FStar_All.pipe_right uu____3567
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
            let uu____3657 =
              let uu____3663 =
                FStar_List.tryFind
                  (fun uu____3678  ->
                     match uu____3678 with
                     | (l,uu____3685) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3663 FStar_Util.must in
            (match uu____3657 with
             | (uu____3710,op) ->
                 let uu____3718 = op arg_tms in (uu____3718, decls))
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
        let uu____3725 = FStar_List.hd args_e in
        match uu____3725 with
        | (tm_sz,uu____3730) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____3739 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____3739 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____3745 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____3745);
                   t_decls) in
            let uu____3746 =
              let uu____3750 = FStar_List.tail args_e in
              encode_args uu____3750 env in
            (match uu____3746 with
             | (arg_tms,decls) ->
                 let head_fv =
                   match head1.FStar_Syntax_Syntax.n with
                   | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                   | uu____3760 -> failwith "Impossible" in
                 let unary arg_tms1 =
                   let uu____3767 = FStar_List.hd arg_tms1 in
                   FStar_SMTEncoding_Term.unboxBitVec sz uu____3767 in
                 let unary_arith arg_tms1 =
                   let uu____3774 = FStar_List.hd arg_tms1 in
                   FStar_SMTEncoding_Term.unboxInt uu____3774 in
                 let binary arg_tms1 =
                   let uu____3783 =
                     let uu____3784 = FStar_List.hd arg_tms1 in
                     FStar_SMTEncoding_Term.unboxBitVec sz uu____3784 in
                   let uu____3785 =
                     let uu____3786 =
                       let uu____3787 = FStar_List.tl arg_tms1 in
                       FStar_List.hd uu____3787 in
                     FStar_SMTEncoding_Term.unboxBitVec sz uu____3786 in
                   (uu____3783, uu____3785) in
                 let binary_arith arg_tms1 =
                   let uu____3797 =
                     let uu____3798 = FStar_List.hd arg_tms1 in
                     FStar_SMTEncoding_Term.unboxBitVec sz uu____3798 in
                   let uu____3799 =
                     let uu____3800 =
                       let uu____3801 = FStar_List.tl arg_tms1 in
                       FStar_List.hd uu____3801 in
                     FStar_SMTEncoding_Term.unboxInt uu____3800 in
                   (uu____3797, uu____3799) in
                 let mk_bv op mk_args ts =
                   let uu____3835 =
                     let uu____3836 = mk_args ts in op uu____3836 in
                   FStar_All.pipe_right uu____3835
                     (FStar_SMTEncoding_Term.boxBitVec sz) in
                 let bv_and = mk_bv FStar_SMTEncoding_Util.mkBvAnd binary in
                 let bv_xor = mk_bv FStar_SMTEncoding_Util.mkBvXor binary in
                 let bv_or = mk_bv FStar_SMTEncoding_Util.mkBvOr binary in
                 let bv_shl =
                   mk_bv (FStar_SMTEncoding_Util.mkBvShl sz) binary_arith in
                 let bv_shr =
                   mk_bv (FStar_SMTEncoding_Util.mkBvShr sz) binary_arith in
                 let bv_udiv =
                   mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz) binary_arith in
                 let bv_mod =
                   mk_bv (FStar_SMTEncoding_Util.mkBvMod sz) binary_arith in
                 let bv_mul =
                   mk_bv (FStar_SMTEncoding_Util.mkBvMul sz) binary_arith in
                 let bv_ult = mk_bv FStar_SMTEncoding_Util.mkBvUlt binary in
                 let bv_to =
                   mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz) unary_arith in
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
                   (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                 let uu____3987 =
                   let uu____3993 =
                     FStar_List.tryFind
                       (fun uu____4008  ->
                          match uu____4008 with
                          | (l,uu____4015) ->
                              FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
                   FStar_All.pipe_right uu____3993 FStar_Util.must in
                 (match uu____3987 with
                  | (uu____4041,op) ->
                      let uu____4049 = op arg_tms in
                      (uu____4049, (FStar_List.append sz_decls decls))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____4057 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____4057
       then
         let uu____4058 = FStar_Syntax_Print.tag_of_term t in
         let uu____4059 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____4060 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4058 uu____4059
           uu____4060
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4064 ->
           let uu____4079 =
             let uu____4080 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4081 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4082 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4083 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4080
               uu____4081 uu____4082 uu____4083 in
           failwith uu____4079
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4086 =
             let uu____4087 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4088 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4089 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4090 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4087
               uu____4088 uu____4089 uu____4090 in
           failwith uu____4086
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4094 =
             let uu____4095 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4095 in
           failwith uu____4094
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____4100) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4130) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4139 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____4139, [])
       | FStar_Syntax_Syntax.Tm_type uu____4141 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4144) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____4150 = encode_const c in (uu____4150, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____4165 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____4165 with
            | (binders1,res) ->
                let uu____4172 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____4172
                then
                  let uu____4175 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____4175 with
                   | (vars,guards,env',decls,uu____4190) ->
                       let fsym =
                         let uu____4200 = varops.fresh "f" in
                         (uu____4200, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____4203 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_4209 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_4209.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_4209.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_4209.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_4209.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_4209.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_4209.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_4209.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_4209.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_4209.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_4209.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_4209.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_4209.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_4209.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_4209.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_4209.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_4209.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_4209.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_4209.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_4209.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_4209.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_4209.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_4209.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_4209.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_4209.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_4209.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_4209.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____4203 with
                        | (pre_opt,res_t) ->
                            let uu____4216 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____4216 with
                             | (res_pred,decls') ->
                                 let uu____4223 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4230 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____4230, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4233 =
                                         encode_formula pre env' in
                                       (match uu____4233 with
                                        | (guard,decls0) ->
                                            let uu____4241 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____4241, decls0)) in
                                 (match uu____4223 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4249 =
                                          let uu____4255 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____4255) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4249 in
                                      let cvars =
                                        let uu____4265 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____4265
                                          (FStar_List.filter
                                             (fun uu____4274  ->
                                                match uu____4274 with
                                                | (x,uu____4278) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4289 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4289 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4294 =
                                             let uu____4295 =
                                               let uu____4299 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____4299) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4295 in
                                           (uu____4294,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4310 =
                                               let uu____4311 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4311 in
                                             varops.mk_unique uu____4310 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____4318 =
                                               FStar_Options.log_queries () in
                                             if uu____4318
                                             then
                                               let uu____4320 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4320
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____4326 =
                                               let uu____4330 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____4330) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4326 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____4338 =
                                               let uu____4342 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____4342,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4338 in
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
                                             let uu____4355 =
                                               let uu____4359 =
                                                 let uu____4360 =
                                                   let uu____4366 =
                                                     let uu____4367 =
                                                       let uu____4370 =
                                                         let uu____4371 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4371 in
                                                       (f_has_t, uu____4370) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4367 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4366) in
                                                 mkForall_fuel uu____4360 in
                                               (uu____4359,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4355 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____4384 =
                                               let uu____4388 =
                                                 let uu____4389 =
                                                   let uu____4395 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4395) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____4389 in
                                               (uu____4388,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4384 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____4409 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____4409);
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
                     let uu____4420 =
                       let uu____4424 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____4424,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4420 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____4433 =
                       let uu____4437 =
                         let uu____4438 =
                           let uu____4444 =
                             let uu____4445 =
                               let uu____4448 =
                                 let uu____4449 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4449 in
                               (f_has_t, uu____4448) in
                             FStar_SMTEncoding_Util.mkImp uu____4445 in
                           ([[f_has_t]], [fsym], uu____4444) in
                         mkForall_fuel uu____4438 in
                       (uu____4437, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4433 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4463 ->
           let uu____4468 =
             let uu____4471 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____4471 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____4476;
                 FStar_Syntax_Syntax.pos = uu____4477;
                 FStar_Syntax_Syntax.vars = uu____4478;_} ->
                 let uu____4485 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____4485 with
                  | (b,f1) ->
                      let uu____4499 =
                        let uu____4500 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____4500 in
                      (uu____4499, f1))
             | uu____4505 -> failwith "impossible" in
           (match uu____4468 with
            | (x,f) ->
                let uu____4512 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4512 with
                 | (base_t,decls) ->
                     let uu____4519 = gen_term_var env x in
                     (match uu____4519 with
                      | (x1,xtm,env') ->
                          let uu____4528 = encode_formula f env' in
                          (match uu____4528 with
                           | (refinement,decls') ->
                               let uu____4535 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4535 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4546 =
                                        let uu____4548 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4552 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4548
                                          uu____4552 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4546 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4571  ->
                                              match uu____4571 with
                                              | (y,uu____4575) ->
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
                                    let uu____4594 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4594 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4599 =
                                           let uu____4600 =
                                             let uu____4604 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4604) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4600 in
                                         (uu____4599,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____4616 =
                                             let uu____4617 =
                                               let uu____4618 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4618 in
                                             Prims.strcat module_name
                                               uu____4617 in
                                           varops.mk_unique uu____4616 in
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
                                           let uu____4627 =
                                             let uu____4631 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4631) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4627 in
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
                                           let uu____4642 =
                                             let uu____4646 =
                                               let uu____4647 =
                                                 let uu____4653 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4653) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4647 in
                                             (uu____4646,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4642 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4668 =
                                             let uu____4672 =
                                               let uu____4673 =
                                                 let uu____4679 =
                                                   let uu____4680 =
                                                     let uu____4683 =
                                                       let uu____4684 =
                                                         let uu____4690 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4690) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4684 in
                                                     (uu____4683, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4680 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4679) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4673 in
                                             (uu____4672,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4668 in
                                         let t_kinding =
                                           let uu____4710 =
                                             let uu____4714 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4714,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4710 in
                                         let t_interp =
                                           let uu____4724 =
                                             let uu____4728 =
                                               let uu____4729 =
                                                 let uu____4735 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4735) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4729 in
                                             let uu____4747 =
                                               let uu____4749 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4749 in
                                             (uu____4728, uu____4747,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4724 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4754 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4754);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4775 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4775 in
           let uu____4776 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____4776 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4784 =
                    let uu____4788 =
                      let uu____4789 =
                        let uu____4790 =
                          let uu____4791 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4791 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4790 in
                      varops.mk_unique uu____4789 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4788) in
                  FStar_SMTEncoding_Util.mkAssume uu____4784 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4794 ->
           let uu____4804 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4804 with
            | (head1,args_e) ->
                let uu____4832 =
                  let uu____4840 =
                    let uu____4841 = FStar_Syntax_Subst.compress head1 in
                    uu____4841.FStar_Syntax_Syntax.n in
                  (uu____4840, args_e) in
                (match uu____4832 with
                 | uu____4851 when head_redex env head1 ->
                     let uu____4859 = whnf env t in
                     encode_term uu____4859 env
                 | uu____4860 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____4872 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____4881;
                       FStar_Syntax_Syntax.pos = uu____4882;
                       FStar_Syntax_Syntax.vars = uu____4883;_},uu____4884),uu____4885::
                    (v1,uu____4887)::(v2,uu____4889)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4927 = encode_term v1 env in
                     (match uu____4927 with
                      | (v11,decls1) ->
                          let uu____4934 = encode_term v2 env in
                          (match uu____4934 with
                           | (v21,decls2) ->
                               let uu____4941 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4941,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4944::(v1,uu____4946)::(v2,uu____4948)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4982 = encode_term v1 env in
                     (match uu____4982 with
                      | (v11,decls1) ->
                          let uu____4989 = encode_term v2 env in
                          (match uu____4989 with
                           | (v21,decls2) ->
                               let uu____4996 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4996,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4998) ->
                     let e0 =
                       let uu____5010 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____5010 in
                     ((let uu____5016 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____5016
                       then
                         let uu____5017 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5017
                       else ());
                      (let e =
                         let uu____5022 =
                           let uu____5023 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____5024 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5023
                             uu____5024 in
                         uu____5022 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5033),(arg,uu____5035)::[]) -> encode_term arg env
                 | uu____5053 ->
                     let uu____5061 = encode_args args_e env in
                     (match uu____5061 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5094 = encode_term head1 env in
                            match uu____5094 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5133 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____5133 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5183  ->
                                                 fun uu____5184  ->
                                                   match (uu____5183,
                                                           uu____5184)
                                                   with
                                                   | ((bv,uu____5198),
                                                      (a,uu____5200)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____5214 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____5214
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____5219 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____5219 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____5229 =
                                                   let uu____5233 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____5238 =
                                                     let uu____5239 =
                                                       let uu____5240 =
                                                         let uu____5241 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____5241 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5240 in
                                                     varops.mk_unique
                                                       uu____5239 in
                                                   (uu____5233,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5238) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5229 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____5252 = lookup_free_var_sym env fv in
                            match uu____5252 with
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
                                   FStar_Syntax_Syntax.tk = uu____5273;
                                   FStar_Syntax_Syntax.pos = uu____5274;
                                   FStar_Syntax_Syntax.vars = uu____5275;_},uu____5276)
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
                                   FStar_Syntax_Syntax.tk = uu____5287;
                                   FStar_Syntax_Syntax.pos = uu____5288;
                                   FStar_Syntax_Syntax.vars = uu____5289;_},uu____5290)
                                ->
                                let uu____5295 =
                                  let uu____5296 =
                                    let uu____5299 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5299
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5296
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5295
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5315 =
                                  let uu____5316 =
                                    let uu____5319 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5319
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5316
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5315
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5334,(FStar_Util.Inl t1,uu____5336),uu____5337)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5375,(FStar_Util.Inr c,uu____5377),uu____5378)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5416 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5436 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5436 in
                               let uu____5437 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____5437 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____5447;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5448;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5449;_},uu____5450)
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
                                     | uu____5476 ->
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
           let uu____5516 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____5516 with
            | (bs1,body1,opening) ->
                let fallback uu____5531 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____5536 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____5536, [decl]) in
                let is_impure rc =
                  let uu____5542 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____5542 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5551 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5551
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____5564 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____5564
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____5567 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____5567)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5572 =
                         let uu____5573 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5573 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5572);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____5575 =
                       (is_impure rc) &&
                         (let uu____5577 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____5577) in
                     if uu____5575
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5582 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____5582 with
                        | (vars,guards,envbody,decls,uu____5597) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____5605 = encode_term body2 envbody in
                            (match uu____5605 with
                             | (body3,decls') ->
                                 let uu____5612 =
                                   let uu____5617 = codomain_eff rc in
                                   match uu____5617 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____5629 = encode_term tfun env in
                                       (match uu____5629 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____5612 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5648 =
                                          let uu____5654 =
                                            let uu____5655 =
                                              let uu____5658 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____5658, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5655 in
                                          ([], vars, uu____5654) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5648 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____5666 =
                                              let uu____5668 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____5668
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5666 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____5679 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____5679 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5684 =
                                             let uu____5685 =
                                               let uu____5689 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5689) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5685 in
                                           (uu____5684,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5695 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____5695 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5702 =
                                                    let uu____5703 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____5703 = cache_size in
                                                  if uu____5702
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
                                                    let uu____5714 =
                                                      let uu____5715 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5715 in
                                                    varops.mk_unique
                                                      uu____5714 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____5720 =
                                                    let uu____5724 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____5724) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5720 in
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
                                                      let uu____5736 =
                                                        let uu____5737 =
                                                          let uu____5741 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____5741,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5737 in
                                                      [uu____5736] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____5749 =
                                                    let uu____5753 =
                                                      let uu____5754 =
                                                        let uu____5760 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5760) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5754 in
                                                    (uu____5753,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5749 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____5770 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5770);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5772,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5773;
                          FStar_Syntax_Syntax.lbunivs = uu____5774;
                          FStar_Syntax_Syntax.lbtyp = uu____5775;
                          FStar_Syntax_Syntax.lbeff = uu____5776;
                          FStar_Syntax_Syntax.lbdef = uu____5777;_}::uu____5778),uu____5779)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5797;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5799;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5815 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____5828 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5828, [decl_e])))
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
              let uu____5868 = encode_term e1 env in
              match uu____5868 with
              | (ee1,decls1) ->
                  let uu____5875 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____5875 with
                   | (xs,e21) ->
                       let uu____5889 = FStar_List.hd xs in
                       (match uu____5889 with
                        | (x1,uu____5897) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5899 = encode_body e21 env' in
                            (match uu____5899 with
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
            let uu____5921 =
              let uu____5925 =
                let uu____5926 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5926 in
              gen_term_var env uu____5925 in
            match uu____5921 with
            | (scrsym,scr',env1) ->
                let uu____5936 = encode_term e env1 in
                (match uu____5936 with
                 | (scr,decls) ->
                     let uu____5943 =
                       let encode_branch b uu____5959 =
                         match uu____5959 with
                         | (else_case,decls1) ->
                             let uu____5970 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5970 with
                              | (p,w,br) ->
                                  let uu____5989 = encode_pat env1 p in
                                  (match uu____5989 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____6013  ->
                                                   match uu____6013 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____6018 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6033 =
                                               encode_term w1 env2 in
                                             (match uu____6033 with
                                              | (w2,decls2) ->
                                                  let uu____6041 =
                                                    let uu____6042 =
                                                      let uu____6045 =
                                                        let uu____6046 =
                                                          let uu____6049 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____6049) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6046 in
                                                      (guard, uu____6045) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6042 in
                                                  (uu____6041, decls2)) in
                                       (match uu____6018 with
                                        | (guard1,decls2) ->
                                            let uu____6057 =
                                              encode_br br env2 in
                                            (match uu____6057 with
                                             | (br1,decls3) ->
                                                 let uu____6065 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____6065,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____5943 with
                      | (match_tm,decls1) ->
                          let uu____6076 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____6076, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____6098 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____6098
       then
         let uu____6099 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6099
       else ());
      (let uu____6101 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____6101 with
       | (vars,pat_term) ->
           let uu____6111 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____6142  ->
                     fun v1  ->
                       match uu____6142 with
                       | (env1,vars1) ->
                           let uu____6170 = gen_term_var env1 v1 in
                           (match uu____6170 with
                            | (xx,uu____6182,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____6111 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____6227 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____6228 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____6229 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____6235 =
                        let uu____6238 = encode_const c in
                        (scrutinee, uu____6238) in
                      FStar_SMTEncoding_Util.mkEq uu____6235
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____6251 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____6251 with
                        | (uu____6255,uu____6256::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____6258 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6279  ->
                                  match uu____6279 with
                                  | (arg,uu____6284) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____6288 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____6288)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____6306) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____6325 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____6338 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6364  ->
                                  match uu____6364 with
                                  | (arg,uu____6372) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____6376 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____6376)) in
                      FStar_All.pipe_right uu____6338 FStar_List.flatten in
                let pat_term1 uu____6392 = encode_term pat_term env1 in
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
      let uu____6399 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____6423  ->
                fun uu____6424  ->
                  match (uu____6423, uu____6424) with
                  | ((tms,decls),(t,uu____6444)) ->
                      let uu____6455 = encode_term t env in
                      (match uu____6455 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____6399 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____6489 = FStar_Syntax_Util.list_elements e in
        match uu____6489 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____6504 =
          let uu____6514 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____6514 FStar_Syntax_Util.head_and_args in
        match uu____6504 with
        | (head1,args) ->
            let uu____6542 =
              let uu____6550 =
                let uu____6551 = FStar_Syntax_Util.un_uinst head1 in
                uu____6551.FStar_Syntax_Syntax.n in
              (uu____6550, args) in
            (match uu____6542 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6562,uu____6563)::(e,uu____6565)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____6591 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6618 =
            let uu____6628 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6628 FStar_Syntax_Util.head_and_args in
          match uu____6618 with
          | (head1,args) ->
              let uu____6657 =
                let uu____6665 =
                  let uu____6666 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6666.FStar_Syntax_Syntax.n in
                (uu____6665, args) in
              (match uu____6657 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6679)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____6699 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____6714 = smt_pat_or1 t1 in
            (match uu____6714 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____6727 = list_elements1 e in
                 FStar_All.pipe_right uu____6727
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6740 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6740
                           (FStar_List.map one_pat)))
             | uu____6748 ->
                 let uu____6752 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6752])
        | uu____6768 ->
            let uu____6770 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6770] in
      let uu____6786 =
        let uu____6799 =
          let uu____6800 = FStar_Syntax_Subst.compress t in
          uu____6800.FStar_Syntax_Syntax.n in
        match uu____6799 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6827 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6827 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6856;
                        FStar_Syntax_Syntax.effect_name = uu____6857;
                        FStar_Syntax_Syntax.result_typ = uu____6858;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6860)::(post,uu____6862)::(pats,uu____6864)::[];
                        FStar_Syntax_Syntax.flags = uu____6865;_}
                      ->
                      let uu____6897 = lemma_pats pats in
                      (binders1, pre, post, uu____6897)
                  | uu____6910 -> failwith "impos"))
        | uu____6923 -> failwith "Impos" in
      match uu____6786 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6959 = env in
            {
              bindings = (uu___136_6959.bindings);
              depth = (uu___136_6959.depth);
              tcenv = (uu___136_6959.tcenv);
              warn = (uu___136_6959.warn);
              cache = (uu___136_6959.cache);
              nolabels = (uu___136_6959.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6959.encode_non_total_function_typ);
              current_module_name = (uu___136_6959.current_module_name)
            } in
          let uu____6960 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____6960 with
           | (vars,guards,env2,decls,uu____6975) ->
               let uu____6982 =
                 let uu____6989 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____7015 =
                             let uu____7020 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____7020 FStar_List.unzip in
                           match uu____7015 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6989 FStar_List.unzip in
               (match uu____6982 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_7079 = env2 in
                      {
                        bindings = (uu___137_7079.bindings);
                        depth = (uu___137_7079.depth);
                        tcenv = (uu___137_7079.tcenv);
                        warn = (uu___137_7079.warn);
                        cache = (uu___137_7079.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_7079.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_7079.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_7079.current_module_name)
                      } in
                    let uu____7080 =
                      let uu____7083 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____7083 env3 in
                    (match uu____7080 with
                     | (pre1,decls'') ->
                         let uu____7088 =
                           let uu____7091 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____7091 env3 in
                         (match uu____7088 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____7098 =
                                let uu____7099 =
                                  let uu____7105 =
                                    let uu____7106 =
                                      let uu____7109 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____7109, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____7106 in
                                  (pats, vars, uu____7105) in
                                FStar_SMTEncoding_Util.mkForall uu____7099 in
                              (uu____7098, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____7122 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____7122
        then
          let uu____7123 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____7124 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____7123 uu____7124
        else () in
      let enc f r l =
        let uu____7151 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____7169 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____7169 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____7151 with
        | (decls,args) ->
            let uu____7186 =
              let uu___138_7187 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_7187.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_7187.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____7186, decls) in
      let const_op f r uu____7212 = let uu____7221 = f r in (uu____7221, []) in
      let un_op f l =
        let uu____7237 = FStar_List.hd l in FStar_All.pipe_left f uu____7237 in
      let bin_op f uu___112_7250 =
        match uu___112_7250 with
        | t1::t2::[] -> f (t1, t2)
        | uu____7258 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____7285 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____7301  ->
                 match uu____7301 with
                 | (t,uu____7309) ->
                     let uu____7310 = encode_formula t env in
                     (match uu____7310 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____7285 with
        | (decls,phis) ->
            let uu____7327 =
              let uu___139_7328 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_7328.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_7328.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____7327, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____7371  ->
               match uu____7371 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____7385) -> false
                    | uu____7386 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____7399 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____7399
        else
          (let uu____7414 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____7414 r rf) in
      let mk_imp1 r uu___113_7433 =
        match uu___113_7433 with
        | (lhs,uu____7437)::(rhs,uu____7439)::[] ->
            let uu____7460 = encode_formula rhs env in
            (match uu____7460 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____7469) ->
                      (l1, decls1)
                  | uu____7472 ->
                      let uu____7473 = encode_formula lhs env in
                      (match uu____7473 with
                       | (l2,decls2) ->
                           let uu____7480 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____7480, (FStar_List.append decls1 decls2)))))
        | uu____7482 -> failwith "impossible" in
      let mk_ite r uu___114_7497 =
        match uu___114_7497 with
        | (guard,uu____7501)::(_then,uu____7503)::(_else,uu____7505)::[] ->
            let uu____7534 = encode_formula guard env in
            (match uu____7534 with
             | (g,decls1) ->
                 let uu____7541 = encode_formula _then env in
                 (match uu____7541 with
                  | (t,decls2) ->
                      let uu____7548 = encode_formula _else env in
                      (match uu____7548 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7557 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7576 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7576 in
      let connectives =
        let uu____7588 =
          let uu____7597 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____7597) in
        let uu____7610 =
          let uu____7620 =
            let uu____7629 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____7629) in
          let uu____7642 =
            let uu____7652 =
              let uu____7662 =
                let uu____7671 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____7671) in
              let uu____7684 =
                let uu____7694 =
                  let uu____7704 =
                    let uu____7713 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____7713) in
                  [uu____7704;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____7694 in
              uu____7662 :: uu____7684 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____7652 in
          uu____7620 :: uu____7642 in
        uu____7588 :: uu____7610 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7929 = encode_formula phi' env in
            (match uu____7929 with
             | (phi2,decls) ->
                 let uu____7936 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7936, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7937 ->
            let uu____7942 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7942 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7969 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7969 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7977;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7979;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7995 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7995 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8027::(x,uu____8029)::(t,uu____8031)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8065 = encode_term x env in
                 (match uu____8065 with
                  | (x1,decls) ->
                      let uu____8072 = encode_term t env in
                      (match uu____8072 with
                       | (t1,decls') ->
                           let uu____8079 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____8079, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____8083)::(msg,uu____8085)::(phi2,uu____8087)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____8121 =
                   let uu____8124 =
                     let uu____8125 = FStar_Syntax_Subst.compress r in
                     uu____8125.FStar_Syntax_Syntax.n in
                   let uu____8128 =
                     let uu____8129 = FStar_Syntax_Subst.compress msg in
                     uu____8129.FStar_Syntax_Syntax.n in
                   (uu____8124, uu____8128) in
                 (match uu____8121 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____8136))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____8148 -> fallback phi2)
             | uu____8151 when head_redex env head2 ->
                 let uu____8159 = whnf env phi1 in
                 encode_formula uu____8159 env
             | uu____8160 ->
                 let uu____8168 = encode_term phi1 env in
                 (match uu____8168 with
                  | (tt,decls) ->
                      let uu____8175 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_8178 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_8178.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_8178.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____8175, decls)))
        | uu____8181 ->
            let uu____8182 = encode_term phi1 env in
            (match uu____8182 with
             | (tt,decls) ->
                 let uu____8189 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_8192 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_8192.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_8192.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____8189, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____8219 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____8219 with
        | (vars,guards,env2,decls,uu____8241) ->
            let uu____8248 =
              let uu____8255 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____8282 =
                          let uu____8287 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____8304  ->
                                    match uu____8304 with
                                    | (t,uu____8310) ->
                                        encode_term t
                                          (let uu___142_8312 = env2 in
                                           {
                                             bindings =
                                               (uu___142_8312.bindings);
                                             depth = (uu___142_8312.depth);
                                             tcenv = (uu___142_8312.tcenv);
                                             warn = (uu___142_8312.warn);
                                             cache = (uu___142_8312.cache);
                                             nolabels =
                                               (uu___142_8312.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_8312.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_8312.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____8287 FStar_List.unzip in
                        match uu____8282 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____8255 FStar_List.unzip in
            (match uu____8248 with
             | (pats,decls') ->
                 let uu____8364 = encode_formula body env2 in
                 (match uu____8364 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____8383;
                             FStar_SMTEncoding_Term.rng = uu____8384;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____8392 -> guards in
                      let uu____8395 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____8395, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____8432  ->
                   match uu____8432 with
                   | (x,uu____8436) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____8442 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____8451 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____8451) uu____8442 tl1 in
             let uu____8453 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____8469  ->
                       match uu____8469 with
                       | (b,uu____8473) ->
                           let uu____8474 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____8474)) in
             (match uu____8453 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____8478) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____8490 =
                    let uu____8491 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____8491 in
                  FStar_Errors.warn pos uu____8490) in
       let uu____8492 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____8492 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____8498 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____8537  ->
                     match uu____8537 with
                     | (l,uu____8547) -> FStar_Ident.lid_equals op l)) in
           (match uu____8498 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____8570,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8599 = encode_q_body env vars pats body in
             match uu____8599 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8625 =
                     let uu____8631 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8631) in
                   FStar_SMTEncoding_Term.mkForall uu____8625
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8643 = encode_q_body env vars pats body in
             match uu____8643 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8668 =
                   let uu____8669 =
                     let uu____8675 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8675) in
                   FStar_SMTEncoding_Term.mkExists uu____8669
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8668, decls))))
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
  let uu____8754 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8754 with
  | (asym,a) ->
      let uu____8759 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8759 with
       | (xsym,x) ->
           let uu____8764 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8764 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8794 =
                      let uu____8800 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____8800, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8794 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____8815 =
                      let uu____8819 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8819) in
                    FStar_SMTEncoding_Util.mkApp uu____8815 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8827 =
                    let uu____8829 =
                      let uu____8831 =
                        let uu____8833 =
                          let uu____8834 =
                            let uu____8838 =
                              let uu____8839 =
                                let uu____8845 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8845) in
                              FStar_SMTEncoding_Util.mkForall uu____8839 in
                            (uu____8838, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8834 in
                        let uu____8854 =
                          let uu____8856 =
                            let uu____8857 =
                              let uu____8861 =
                                let uu____8862 =
                                  let uu____8868 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____8868) in
                                FStar_SMTEncoding_Util.mkForall uu____8862 in
                              (uu____8861,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____8857 in
                          [uu____8856] in
                        uu____8833 :: uu____8854 in
                      xtok_decl :: uu____8831 in
                    xname_decl :: uu____8829 in
                  (xtok1, uu____8827) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____8917 =
                    let uu____8925 =
                      let uu____8931 =
                        let uu____8932 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8932 in
                      quant axy uu____8931 in
                    (FStar_Parser_Const.op_Eq, uu____8925) in
                  let uu____8938 =
                    let uu____8947 =
                      let uu____8955 =
                        let uu____8961 =
                          let uu____8962 =
                            let uu____8963 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8963 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8962 in
                        quant axy uu____8961 in
                      (FStar_Parser_Const.op_notEq, uu____8955) in
                    let uu____8969 =
                      let uu____8978 =
                        let uu____8986 =
                          let uu____8992 =
                            let uu____8993 =
                              let uu____8994 =
                                let uu____8997 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8998 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8997, uu____8998) in
                              FStar_SMTEncoding_Util.mkLT uu____8994 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8993 in
                          quant xy uu____8992 in
                        (FStar_Parser_Const.op_LT, uu____8986) in
                      let uu____9004 =
                        let uu____9013 =
                          let uu____9021 =
                            let uu____9027 =
                              let uu____9028 =
                                let uu____9029 =
                                  let uu____9032 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____9033 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____9032, uu____9033) in
                                FStar_SMTEncoding_Util.mkLTE uu____9029 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____9028 in
                            quant xy uu____9027 in
                          (FStar_Parser_Const.op_LTE, uu____9021) in
                        let uu____9039 =
                          let uu____9048 =
                            let uu____9056 =
                              let uu____9062 =
                                let uu____9063 =
                                  let uu____9064 =
                                    let uu____9067 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____9068 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____9067, uu____9068) in
                                  FStar_SMTEncoding_Util.mkGT uu____9064 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____9063 in
                              quant xy uu____9062 in
                            (FStar_Parser_Const.op_GT, uu____9056) in
                          let uu____9074 =
                            let uu____9083 =
                              let uu____9091 =
                                let uu____9097 =
                                  let uu____9098 =
                                    let uu____9099 =
                                      let uu____9102 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____9103 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____9102, uu____9103) in
                                    FStar_SMTEncoding_Util.mkGTE uu____9099 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____9098 in
                                quant xy uu____9097 in
                              (FStar_Parser_Const.op_GTE, uu____9091) in
                            let uu____9109 =
                              let uu____9118 =
                                let uu____9126 =
                                  let uu____9132 =
                                    let uu____9133 =
                                      let uu____9134 =
                                        let uu____9137 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____9138 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____9137, uu____9138) in
                                      FStar_SMTEncoding_Util.mkSub uu____9134 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____9133 in
                                  quant xy uu____9132 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____9126) in
                              let uu____9144 =
                                let uu____9153 =
                                  let uu____9161 =
                                    let uu____9167 =
                                      let uu____9168 =
                                        let uu____9169 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____9169 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____9168 in
                                    quant qx uu____9167 in
                                  (FStar_Parser_Const.op_Minus, uu____9161) in
                                let uu____9175 =
                                  let uu____9184 =
                                    let uu____9192 =
                                      let uu____9198 =
                                        let uu____9199 =
                                          let uu____9200 =
                                            let uu____9203 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____9204 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____9203, uu____9204) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____9200 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____9199 in
                                      quant xy uu____9198 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____9192) in
                                  let uu____9210 =
                                    let uu____9219 =
                                      let uu____9227 =
                                        let uu____9233 =
                                          let uu____9234 =
                                            let uu____9235 =
                                              let uu____9238 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____9239 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____9238, uu____9239) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____9235 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____9234 in
                                        quant xy uu____9233 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____9227) in
                                    let uu____9245 =
                                      let uu____9254 =
                                        let uu____9262 =
                                          let uu____9268 =
                                            let uu____9269 =
                                              let uu____9270 =
                                                let uu____9273 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____9274 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____9273, uu____9274) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____9270 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____9269 in
                                          quant xy uu____9268 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____9262) in
                                      let uu____9280 =
                                        let uu____9289 =
                                          let uu____9297 =
                                            let uu____9303 =
                                              let uu____9304 =
                                                let uu____9305 =
                                                  let uu____9308 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____9309 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____9308, uu____9309) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____9305 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____9304 in
                                            quant xy uu____9303 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____9297) in
                                        let uu____9315 =
                                          let uu____9324 =
                                            let uu____9332 =
                                              let uu____9338 =
                                                let uu____9339 =
                                                  let uu____9340 =
                                                    let uu____9343 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____9344 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____9343, uu____9344) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____9340 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____9339 in
                                              quant xy uu____9338 in
                                            (FStar_Parser_Const.op_And,
                                              uu____9332) in
                                          let uu____9350 =
                                            let uu____9359 =
                                              let uu____9367 =
                                                let uu____9373 =
                                                  let uu____9374 =
                                                    let uu____9375 =
                                                      let uu____9378 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____9379 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____9378,
                                                        uu____9379) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____9375 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____9374 in
                                                quant xy uu____9373 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____9367) in
                                            let uu____9385 =
                                              let uu____9394 =
                                                let uu____9402 =
                                                  let uu____9408 =
                                                    let uu____9409 =
                                                      let uu____9410 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____9410 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____9409 in
                                                  quant qx uu____9408 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____9402) in
                                              [uu____9394] in
                                            uu____9359 :: uu____9385 in
                                          uu____9324 :: uu____9350 in
                                        uu____9289 :: uu____9315 in
                                      uu____9254 :: uu____9280 in
                                    uu____9219 :: uu____9245 in
                                  uu____9184 :: uu____9210 in
                                uu____9153 :: uu____9175 in
                              uu____9118 :: uu____9144 in
                            uu____9083 :: uu____9109 in
                          uu____9048 :: uu____9074 in
                        uu____9013 :: uu____9039 in
                      uu____8978 :: uu____9004 in
                    uu____8947 :: uu____8969 in
                  uu____8917 :: uu____8938 in
                let mk1 l v1 =
                  let uu____9538 =
                    let uu____9543 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9578  ->
                              match uu____9578 with
                              | (l',uu____9587) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____9543
                      (FStar_Option.map
                         (fun uu____9623  ->
                            match uu____9623 with | (uu____9634,b) -> b v1)) in
                  FStar_All.pipe_right uu____9538 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9678  ->
                          match uu____9678 with
                          | (l',uu____9687) -> FStar_Ident.lid_equals l l')) in
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
        let uu____9716 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9716 with
        | (xxsym,xx) ->
            let uu____9721 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9721 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____9729 =
                   let uu____9733 =
                     let uu____9734 =
                       let uu____9740 =
                         let uu____9741 =
                           let uu____9744 =
                             let uu____9745 =
                               let uu____9748 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9748) in
                             FStar_SMTEncoding_Util.mkEq uu____9745 in
                           (xx_has_type, uu____9744) in
                         FStar_SMTEncoding_Util.mkImp uu____9741 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9740) in
                     FStar_SMTEncoding_Util.mkForall uu____9734 in
                   let uu____9761 =
                     let uu____9762 =
                       let uu____9763 =
                         let uu____9764 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9764 in
                       Prims.strcat module_name uu____9763 in
                     varops.mk_unique uu____9762 in
                   (uu____9733, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____9761) in
                 FStar_SMTEncoding_Util.mkAssume uu____9729)
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
    let uu____9798 =
      let uu____9799 =
        let uu____9803 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9803, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9799 in
    let uu____9805 =
      let uu____9807 =
        let uu____9808 =
          let uu____9812 =
            let uu____9813 =
              let uu____9819 =
                let uu____9820 =
                  let uu____9823 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9823) in
                FStar_SMTEncoding_Util.mkImp uu____9820 in
              ([[typing_pred]], [xx], uu____9819) in
            mkForall_fuel uu____9813 in
          (uu____9812, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9808 in
      [uu____9807] in
    uu____9798 :: uu____9805 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9851 =
      let uu____9852 =
        let uu____9856 =
          let uu____9857 =
            let uu____9863 =
              let uu____9866 =
                let uu____9868 = FStar_SMTEncoding_Term.boxBool b in
                [uu____9868] in
              [uu____9866] in
            let uu____9871 =
              let uu____9872 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____9872 tt in
            (uu____9863, [bb], uu____9871) in
          FStar_SMTEncoding_Util.mkForall uu____9857 in
        (uu____9856, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9852 in
    let uu____9883 =
      let uu____9885 =
        let uu____9886 =
          let uu____9890 =
            let uu____9891 =
              let uu____9897 =
                let uu____9898 =
                  let uu____9901 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____9901) in
                FStar_SMTEncoding_Util.mkImp uu____9898 in
              ([[typing_pred]], [xx], uu____9897) in
            mkForall_fuel uu____9891 in
          (uu____9890, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9886 in
      [uu____9885] in
    uu____9851 :: uu____9883 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____9935 =
        let uu____9936 =
          let uu____9940 =
            let uu____9942 =
              let uu____9944 =
                let uu____9946 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9947 =
                  let uu____9949 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9949] in
                uu____9946 :: uu____9947 in
              tt :: uu____9944 in
            tt :: uu____9942 in
          ("Prims.Precedes", uu____9940) in
        FStar_SMTEncoding_Util.mkApp uu____9936 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9935 in
    let precedes_y_x =
      let uu____9952 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9952 in
    let uu____9954 =
      let uu____9955 =
        let uu____9959 =
          let uu____9960 =
            let uu____9966 =
              let uu____9969 =
                let uu____9971 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9971] in
              [uu____9969] in
            let uu____9974 =
              let uu____9975 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9975 tt in
            (uu____9966, [bb], uu____9974) in
          FStar_SMTEncoding_Util.mkForall uu____9960 in
        (uu____9959, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9955 in
    let uu____9986 =
      let uu____9988 =
        let uu____9989 =
          let uu____9993 =
            let uu____9994 =
              let uu____10000 =
                let uu____10001 =
                  let uu____10004 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____10004) in
                FStar_SMTEncoding_Util.mkImp uu____10001 in
              ([[typing_pred]], [xx], uu____10000) in
            mkForall_fuel uu____9994 in
          (uu____9993, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9989 in
      let uu____10017 =
        let uu____10019 =
          let uu____10020 =
            let uu____10024 =
              let uu____10025 =
                let uu____10031 =
                  let uu____10032 =
                    let uu____10035 =
                      let uu____10036 =
                        let uu____10038 =
                          let uu____10040 =
                            let uu____10042 =
                              let uu____10043 =
                                let uu____10046 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____10047 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____10046, uu____10047) in
                              FStar_SMTEncoding_Util.mkGT uu____10043 in
                            let uu____10048 =
                              let uu____10050 =
                                let uu____10051 =
                                  let uu____10054 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____10055 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____10054, uu____10055) in
                                FStar_SMTEncoding_Util.mkGTE uu____10051 in
                              let uu____10056 =
                                let uu____10058 =
                                  let uu____10059 =
                                    let uu____10062 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____10063 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____10062, uu____10063) in
                                  FStar_SMTEncoding_Util.mkLT uu____10059 in
                                [uu____10058] in
                              uu____10050 :: uu____10056 in
                            uu____10042 :: uu____10048 in
                          typing_pred_y :: uu____10040 in
                        typing_pred :: uu____10038 in
                      FStar_SMTEncoding_Util.mk_and_l uu____10036 in
                    (uu____10035, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____10032 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____10031) in
              mkForall_fuel uu____10025 in
            (uu____10024,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____10020 in
        [uu____10019] in
      uu____9988 :: uu____10017 in
    uu____9954 :: uu____9986 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____10093 =
      let uu____10094 =
        let uu____10098 =
          let uu____10099 =
            let uu____10105 =
              let uu____10108 =
                let uu____10110 = FStar_SMTEncoding_Term.boxString b in
                [uu____10110] in
              [uu____10108] in
            let uu____10113 =
              let uu____10114 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____10114 tt in
            (uu____10105, [bb], uu____10113) in
          FStar_SMTEncoding_Util.mkForall uu____10099 in
        (uu____10098, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____10094 in
    let uu____10125 =
      let uu____10127 =
        let uu____10128 =
          let uu____10132 =
            let uu____10133 =
              let uu____10139 =
                let uu____10140 =
                  let uu____10143 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____10143) in
                FStar_SMTEncoding_Util.mkImp uu____10140 in
              ([[typing_pred]], [xx], uu____10139) in
            mkForall_fuel uu____10133 in
          (uu____10132, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____10128 in
      [uu____10127] in
    uu____10093 :: uu____10125 in
  let mk_ref1 env reft_name uu____10165 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____10176 =
        let uu____10180 =
          let uu____10182 = FStar_SMTEncoding_Util.mkFreeV aa in
          [uu____10182] in
        (reft_name, uu____10180) in
      FStar_SMTEncoding_Util.mkApp uu____10176 in
    let refb =
      let uu____10185 =
        let uu____10189 =
          let uu____10191 = FStar_SMTEncoding_Util.mkFreeV bb in
          [uu____10191] in
        (reft_name, uu____10189) in
      FStar_SMTEncoding_Util.mkApp uu____10185 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____10195 =
      let uu____10196 =
        let uu____10200 =
          let uu____10201 =
            let uu____10207 =
              let uu____10208 =
                let uu____10211 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____10211) in
              FStar_SMTEncoding_Util.mkImp uu____10208 in
            ([[typing_pred]], [xx; aa], uu____10207) in
          mkForall_fuel uu____10201 in
        (uu____10200, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____10196 in
    [uu____10195] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____10251 =
      let uu____10252 =
        let uu____10256 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____10256, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10252 in
    [uu____10251] in
  let mk_and_interp env conj uu____10267 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10284 =
      let uu____10285 =
        let uu____10289 =
          let uu____10290 =
            let uu____10296 =
              let uu____10297 =
                let uu____10300 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____10300, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10297 in
            ([[l_and_a_b]], [aa; bb], uu____10296) in
          FStar_SMTEncoding_Util.mkForall uu____10290 in
        (uu____10289, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10285 in
    [uu____10284] in
  let mk_or_interp env disj uu____10324 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10341 =
      let uu____10342 =
        let uu____10346 =
          let uu____10347 =
            let uu____10353 =
              let uu____10354 =
                let uu____10357 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____10357, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10354 in
            ([[l_or_a_b]], [aa; bb], uu____10353) in
          FStar_SMTEncoding_Util.mkForall uu____10347 in
        (uu____10346, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10342 in
    [uu____10341] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____10398 =
      let uu____10399 =
        let uu____10403 =
          let uu____10404 =
            let uu____10410 =
              let uu____10411 =
                let uu____10414 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10414, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10411 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____10410) in
          FStar_SMTEncoding_Util.mkForall uu____10404 in
        (uu____10403, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10399 in
    [uu____10398] in
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
    let uu____10461 =
      let uu____10462 =
        let uu____10466 =
          let uu____10467 =
            let uu____10473 =
              let uu____10474 =
                let uu____10477 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10477, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10474 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____10473) in
          FStar_SMTEncoding_Util.mkForall uu____10467 in
        (uu____10466, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10462 in
    [uu____10461] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10522 =
      let uu____10523 =
        let uu____10527 =
          let uu____10528 =
            let uu____10534 =
              let uu____10535 =
                let uu____10538 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____10538, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10535 in
            ([[l_imp_a_b]], [aa; bb], uu____10534) in
          FStar_SMTEncoding_Util.mkForall uu____10528 in
        (uu____10527, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10523 in
    [uu____10522] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10579 =
      let uu____10580 =
        let uu____10584 =
          let uu____10585 =
            let uu____10591 =
              let uu____10592 =
                let uu____10595 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10595, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10592 in
            ([[l_iff_a_b]], [aa; bb], uu____10591) in
          FStar_SMTEncoding_Util.mkForall uu____10585 in
        (uu____10584, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10580 in
    [uu____10579] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____10629 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10629 in
    let uu____10631 =
      let uu____10632 =
        let uu____10636 =
          let uu____10637 =
            let uu____10643 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10643) in
          FStar_SMTEncoding_Util.mkForall uu____10637 in
        (uu____10636, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10632 in
    [uu____10631] in
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
      let uu____10683 =
        let uu____10687 =
          let uu____10689 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10689] in
        ("Valid", uu____10687) in
      FStar_SMTEncoding_Util.mkApp uu____10683 in
    let uu____10691 =
      let uu____10692 =
        let uu____10696 =
          let uu____10697 =
            let uu____10703 =
              let uu____10704 =
                let uu____10707 =
                  let uu____10708 =
                    let uu____10714 =
                      let uu____10717 =
                        let uu____10719 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10719] in
                      [uu____10717] in
                    let uu____10722 =
                      let uu____10723 =
                        let uu____10726 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10726, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10723 in
                    (uu____10714, [xx1], uu____10722) in
                  FStar_SMTEncoding_Util.mkForall uu____10708 in
                (uu____10707, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10704 in
            ([[l_forall_a_b]], [aa; bb], uu____10703) in
          FStar_SMTEncoding_Util.mkForall uu____10697 in
        (uu____10696, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10692 in
    [uu____10691] in
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
      let uu____10777 =
        let uu____10781 =
          let uu____10783 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10783] in
        ("Valid", uu____10781) in
      FStar_SMTEncoding_Util.mkApp uu____10777 in
    let uu____10785 =
      let uu____10786 =
        let uu____10790 =
          let uu____10791 =
            let uu____10797 =
              let uu____10798 =
                let uu____10801 =
                  let uu____10802 =
                    let uu____10808 =
                      let uu____10811 =
                        let uu____10813 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10813] in
                      [uu____10811] in
                    let uu____10816 =
                      let uu____10817 =
                        let uu____10820 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10820, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10817 in
                    (uu____10808, [xx1], uu____10816) in
                  FStar_SMTEncoding_Util.mkExists uu____10802 in
                (uu____10801, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10798 in
            ([[l_exists_a_b]], [aa; bb], uu____10797) in
          FStar_SMTEncoding_Util.mkForall uu____10791 in
        (uu____10790, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10786 in
    [uu____10785] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____10856 =
      let uu____10857 =
        let uu____10861 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____10862 = varops.mk_unique "typing_range_const" in
        (uu____10861, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____10862) in
      FStar_SMTEncoding_Util.mkAssume uu____10857 in
    [uu____10856] in
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
          let uu____11124 =
            FStar_Util.find_opt
              (fun uu____11145  ->
                 match uu____11145 with
                 | (l,uu____11155) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____11124 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____11177,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____11213 = encode_function_type_as_formula t env in
        match uu____11213 with
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
            let uu____11246 =
              (let uu____11249 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____11249) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____11246
            then
              let uu____11253 = new_term_constant_and_tok_from_lid env lid in
              match uu____11253 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____11265 =
                      let uu____11266 = FStar_Syntax_Subst.compress t_norm in
                      uu____11266.FStar_Syntax_Syntax.n in
                    match uu____11265 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11271) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____11289  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____11292 -> [] in
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
              (let uu____11301 = prims.is lid in
               if uu____11301
               then
                 let vname = varops.new_fvar lid in
                 let uu____11306 = prims.mk lid vname in
                 match uu____11306 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____11321 =
                    let uu____11327 = curried_arrow_formals_comp t_norm in
                    match uu____11327 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____11338 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____11338
                          then
                            let uu____11339 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_11342 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_11342.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_11342.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_11342.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_11342.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_11342.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_11342.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_11342.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_11342.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_11342.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_11342.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_11342.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_11342.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_11342.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_11342.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_11342.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_11342.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_11342.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_11342.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_11342.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_11342.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_11342.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_11342.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_11342.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_11342.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_11342.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_11342.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____11339
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____11349 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____11349)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____11321 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____11376 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____11376 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____11389 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_11421  ->
                                     match uu___115_11421 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____11424 =
                                           FStar_Util.prefix vars in
                                         (match uu____11424 with
                                          | (uu____11435,(xxsym,uu____11437))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____11447 =
                                                let uu____11448 =
                                                  let uu____11452 =
                                                    let uu____11453 =
                                                      let uu____11459 =
                                                        let uu____11460 =
                                                          let uu____11463 =
                                                            let uu____11464 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____11464 in
                                                          (vapp, uu____11463) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____11460 in
                                                      ([[vapp]], vars,
                                                        uu____11459) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11453 in
                                                  (uu____11452,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11448 in
                                              [uu____11447])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____11475 =
                                           FStar_Util.prefix vars in
                                         (match uu____11475 with
                                          | (uu____11486,(xxsym,uu____11488))
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
                                              let uu____11502 =
                                                let uu____11503 =
                                                  let uu____11507 =
                                                    let uu____11508 =
                                                      let uu____11514 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____11514) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11508 in
                                                  (uu____11507,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11503 in
                                              [uu____11502])
                                     | uu____11523 -> [])) in
                           let uu____11524 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____11524 with
                            | (vars,guards,env',decls1,uu____11540) ->
                                let uu____11547 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____11552 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____11552, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____11554 = encode_formula p env' in
                                      (match uu____11554 with
                                       | (g,ds) ->
                                           let uu____11561 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____11561,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____11547 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____11570 =
                                         let uu____11574 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____11574) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____11570 in
                                     let uu____11579 =
                                       let vname_decl =
                                         let uu____11584 =
                                           let uu____11590 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11596  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11590,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____11584 in
                                       let uu____11601 =
                                         let env2 =
                                           let uu___144_11605 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11605.bindings);
                                             depth = (uu___144_11605.depth);
                                             tcenv = (uu___144_11605.tcenv);
                                             warn = (uu___144_11605.warn);
                                             cache = (uu___144_11605.cache);
                                             nolabels =
                                               (uu___144_11605.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11605.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11605.current_module_name)
                                           } in
                                         let uu____11606 =
                                           let uu____11607 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11607 in
                                         if uu____11606
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____11601 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11617::uu____11618 ->
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
                                                   let uu____11641 =
                                                     let uu____11647 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11647) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11641 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11661 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____11663 =
                                             match formals with
                                             | [] ->
                                                 let uu____11672 =
                                                   let uu____11673 =
                                                     let uu____11675 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_41)
                                                       uu____11675 in
                                                   push_free_var env1 lid
                                                     vname uu____11673 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11672)
                                             | uu____11678 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____11683 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11683 in
                                                 let name_tok_corr =
                                                   let uu____11685 =
                                                     let uu____11689 =
                                                       let uu____11690 =
                                                         let uu____11696 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11696) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11690 in
                                                     (uu____11689,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11685 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____11663 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____11579 with
                                      | (decls2,env2) ->
                                          let uu____11720 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11725 =
                                              encode_term res_t1 env' in
                                            match uu____11725 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11733 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11733,
                                                  decls) in
                                          (match uu____11720 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11741 =
                                                   let uu____11745 =
                                                     let uu____11746 =
                                                       let uu____11752 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11752) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11746 in
                                                   (uu____11745,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11741 in
                                               let freshness =
                                                 let uu____11761 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11761
                                                 then
                                                   let uu____11764 =
                                                     let uu____11765 =
                                                       let uu____11771 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____11777 =
                                                         varops.next_id () in
                                                       (vname, uu____11771,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11777) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11765 in
                                                   let uu____11779 =
                                                     let uu____11781 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11781] in
                                                   uu____11764 :: uu____11779
                                                 else [] in
                                               let g =
                                                 let uu____11785 =
                                                   let uu____11787 =
                                                     let uu____11789 =
                                                       let uu____11791 =
                                                         let uu____11793 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____11793 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11791 in
                                                     FStar_List.append decls3
                                                       uu____11789 in
                                                   FStar_List.append decls2
                                                     uu____11787 in
                                                 FStar_List.append decls11
                                                   uu____11785 in
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
          let uu____11819 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11819 with
          | FStar_Pervasives_Native.None  ->
              let uu____11838 = encode_free_var env x t t_norm [] in
              (match uu____11838 with
               | (decls,env1) ->
                   let uu____11853 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____11853 with
                    | (n1,x',uu____11868) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____11880) ->
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
          let uu____11917 = encode_free_var env lid t tt quals in
          match uu____11917 with
          | (decls,env1) ->
              let uu____11928 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____11928
              then
                let uu____11932 =
                  let uu____11934 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11934 in
                (uu____11932, env1)
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
             (fun uu____11972  ->
                fun lb  ->
                  match uu____11972 with
                  | (decls,env1) ->
                      let uu____11984 =
                        let uu____11988 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11988
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11984 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____12003 = FStar_Syntax_Util.head_and_args t in
    match uu____12003 with
    | (hd1,args) ->
        let uu____12029 =
          let uu____12030 = FStar_Syntax_Util.un_uinst hd1 in
          uu____12030.FStar_Syntax_Syntax.n in
        (match uu____12029 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____12034,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____12047 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____12065  ->
      fun quals  ->
        match uu____12065 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____12115 = FStar_Util.first_N nbinders formals in
              match uu____12115 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____12164  ->
                         fun uu____12165  ->
                           match (uu____12164, uu____12165) with
                           | ((formal,uu____12175),(binder,uu____12177)) ->
                               let uu____12182 =
                                 let uu____12187 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____12187) in
                               FStar_Syntax_Syntax.NT uu____12182) formals1
                      binders in
                  let extra_formals1 =
                    let uu____12192 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____12210  ->
                              match uu____12210 with
                              | (x,i) ->
                                  let uu____12217 =
                                    let uu___145_12218 = x in
                                    let uu____12219 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_12218.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_12218.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____12219
                                    } in
                                  (uu____12217, i))) in
                    FStar_All.pipe_right uu____12192
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____12231 =
                      let uu____12233 =
                        let uu____12234 = FStar_Syntax_Subst.subst subst1 t in
                        uu____12234.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                        uu____12233 in
                    let uu____12238 =
                      let uu____12239 = FStar_Syntax_Subst.compress body in
                      let uu____12240 =
                        let uu____12241 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____12241 in
                      FStar_Syntax_Syntax.extend_app_n uu____12239
                        uu____12240 in
                    uu____12238 uu____12231 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____12283 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____12283
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_12286 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_12286.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_12286.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_12286.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_12286.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_12286.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_12286.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_12286.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_12286.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_12286.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_12286.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_12286.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_12286.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_12286.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_12286.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_12286.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_12286.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_12286.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_12286.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_12286.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_12286.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_12286.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_12286.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_12286.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_12286.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_12286.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_12286.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____12307 = FStar_Syntax_Util.abs_formals e in
                match uu____12307 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____12341::uu____12342 ->
                         let uu____12350 =
                           let uu____12351 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12351.FStar_Syntax_Syntax.n in
                         (match uu____12350 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12378 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12378 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____12406 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____12406
                                   then
                                     let uu____12429 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____12429 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____12484  ->
                                                   fun uu____12485  ->
                                                     match (uu____12484,
                                                             uu____12485)
                                                     with
                                                     | ((x,uu____12495),
                                                        (b,uu____12497)) ->
                                                         let uu____12502 =
                                                           let uu____12507 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____12507) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____12502)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____12509 =
                                            let uu____12520 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____12520) in
                                          (uu____12509, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____12560 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____12560 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12612) ->
                              let uu____12617 =
                                let uu____12628 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____12628 in
                              (uu____12617, true)
                          | uu____12661 when Prims.op_Negation norm1 ->
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
                          | uu____12663 ->
                              let uu____12664 =
                                let uu____12665 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12666 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12665
                                  uu____12666 in
                              failwith uu____12664)
                     | uu____12679 ->
                         let uu____12680 =
                           let uu____12681 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12681.FStar_Syntax_Syntax.n in
                         (match uu____12680 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12708 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12708 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12726 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12726 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12774 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12804 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____12804
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12812 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____12866  ->
                            fun lb  ->
                              match uu____12866 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____12917 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____12917
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____12920 =
                                      let uu____12928 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____12928
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____12920 with
                                    | (tok,decl,env2) ->
                                        let uu____12953 =
                                          let uu____12960 =
                                            let uu____12966 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12966, tok) in
                                          uu____12960 :: toks in
                                        (uu____12953, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12812 with
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
                        | uu____13068 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____13073 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____13073 vars)
                            else
                              (let uu____13075 =
                                 let uu____13079 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____13079) in
                               FStar_SMTEncoding_Util.mkApp uu____13075) in
                      let uu____13084 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_13087  ->
                                 match uu___116_13087 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____13088 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____13093 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____13093))) in
                      if uu____13084
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____13113;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____13115;
                                FStar_Syntax_Syntax.lbeff = uu____13116;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____13153 =
                                 let uu____13157 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____13157 with
                                 | (tcenv',uu____13168,e_t) ->
                                     let uu____13172 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____13179 -> failwith "Impossible" in
                                     (match uu____13172 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_13189 = env1 in
                                            {
                                              bindings =
                                                (uu___149_13189.bindings);
                                              depth = (uu___149_13189.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_13189.warn);
                                              cache = (uu___149_13189.cache);
                                              nolabels =
                                                (uu___149_13189.nolabels);
                                              use_zfuel_name =
                                                (uu___149_13189.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_13189.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_13189.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____13153 with
                                | (env',e1,t_norm1) ->
                                    let uu____13196 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____13196 with
                                     | ((binders,body,uu____13208,uu____13209),curry)
                                         ->
                                         ((let uu____13216 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____13216
                                           then
                                             let uu____13217 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____13218 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____13217 uu____13218
                                           else ());
                                          (let uu____13220 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____13220 with
                                           | (vars,guards,env'1,binder_decls,uu____13236)
                                               ->
                                               let body1 =
                                                 let uu____13244 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____13244
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____13247 =
                                                 let uu____13252 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____13252
                                                 then
                                                   let uu____13258 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____13259 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____13258, uu____13259)
                                                 else
                                                   (let uu____13265 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____13265)) in
                                               (match uu____13247 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____13279 =
                                                        let uu____13283 =
                                                          let uu____13284 =
                                                            let uu____13290 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____13290) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____13284 in
                                                        let uu____13296 =
                                                          let uu____13298 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____13298 in
                                                        (uu____13283,
                                                          uu____13296,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____13279 in
                                                    let uu____13300 =
                                                      let uu____13302 =
                                                        let uu____13304 =
                                                          let uu____13306 =
                                                            let uu____13308 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____13308 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____13306 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____13304 in
                                                      FStar_List.append
                                                        decls1 uu____13302 in
                                                    (uu____13300, env1))))))
                           | uu____13311 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____13330 = varops.fresh "fuel" in
                             (uu____13330, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____13333 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____13383  ->
                                     fun uu____13384  ->
                                       match (uu____13383, uu____13384) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____13462 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____13462 in
                                           let gtok =
                                             let uu____13464 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____13464 in
                                           let env3 =
                                             let uu____13466 =
                                               let uu____13468 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_43) uu____13468 in
                                             push_free_var env2 flid gtok
                                               uu____13466 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____13333 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____13554
                                 t_norm uu____13556 =
                                 match (uu____13554, uu____13556) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____13583;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____13584;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____13601 =
                                       let uu____13605 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____13605 with
                                       | (tcenv',uu____13620,e_t) ->
                                           let uu____13624 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13631 ->
                                                 failwith "Impossible" in
                                           (match uu____13624 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13641 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13641.bindings);
                                                    depth =
                                                      (uu___150_13641.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13641.warn);
                                                    cache =
                                                      (uu___150_13641.cache);
                                                    nolabels =
                                                      (uu___150_13641.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13641.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13641.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13641.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____13601 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13651 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____13651
                                            then
                                              let uu____13652 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13653 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13654 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13652 uu____13653
                                                uu____13654
                                            else ());
                                           (let uu____13656 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13656 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13678 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____13678
                                                  then
                                                    let uu____13679 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13680 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13681 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13682 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13679 uu____13680
                                                      uu____13681 uu____13682
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13686 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____13686 with
                                                  | (vars,guards,env'1,binder_decls,uu____13704)
                                                      ->
                                                      let decl_g =
                                                        let uu____13712 =
                                                          let uu____13718 =
                                                            let uu____13720 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13720 in
                                                          (g, uu____13718,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13712 in
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
                                                        let uu____13735 =
                                                          let uu____13739 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13739) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13735 in
                                                      let gsapp =
                                                        let uu____13745 =
                                                          let uu____13749 =
                                                            let uu____13751 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13751 ::
                                                              vars_tm in
                                                          (g, uu____13749) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13745 in
                                                      let gmax =
                                                        let uu____13755 =
                                                          let uu____13759 =
                                                            let uu____13761 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13761 ::
                                                              vars_tm in
                                                          (g, uu____13759) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13755 in
                                                      let body1 =
                                                        let uu____13765 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13765
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____13767 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13767 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13778
                                                               =
                                                               let uu____13782
                                                                 =
                                                                 let uu____13783
                                                                   =
                                                                   let uu____13791
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
                                                                    uu____13791) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13783 in
                                                               let uu____13802
                                                                 =
                                                                 let uu____13804
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____13804 in
                                                               (uu____13782,
                                                                 uu____13802,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13778 in
                                                           let eqn_f =
                                                             let uu____13807
                                                               =
                                                               let uu____13811
                                                                 =
                                                                 let uu____13812
                                                                   =
                                                                   let uu____13818
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13818) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13812 in
                                                               (uu____13811,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13807 in
                                                           let eqn_g' =
                                                             let uu____13826
                                                               =
                                                               let uu____13830
                                                                 =
                                                                 let uu____13831
                                                                   =
                                                                   let uu____13837
                                                                    =
                                                                    let uu____13838
                                                                    =
                                                                    let uu____13841
                                                                    =
                                                                    let uu____13842
                                                                    =
                                                                    let uu____13846
                                                                    =
                                                                    let uu____13848
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____13848
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13846) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13842 in
                                                                    (gsapp,
                                                                    uu____13841) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13838 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13837) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13831 in
                                                               (uu____13830,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13826 in
                                                           let uu____13860 =
                                                             let uu____13865
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____13865
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____13882)
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
                                                                    let uu____13897
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____13897
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____13900
                                                                    =
                                                                    let uu____13904
                                                                    =
                                                                    let uu____13905
                                                                    =
                                                                    let uu____13911
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13911) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13905 in
                                                                    (uu____13904,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13900 in
                                                                 let uu____13922
                                                                   =
                                                                   let uu____13926
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____13926
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____13934
                                                                    =
                                                                    let uu____13936
                                                                    =
                                                                    let uu____13937
                                                                    =
                                                                    let uu____13941
                                                                    =
                                                                    let uu____13942
                                                                    =
                                                                    let uu____13948
                                                                    =
                                                                    let uu____13949
                                                                    =
                                                                    let uu____13952
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____13952,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13949 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13948) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13942 in
                                                                    (uu____13941,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13937 in
                                                                    [uu____13936] in
                                                                    (d3,
                                                                    uu____13934) in
                                                                 (match uu____13922
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____13860
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
                               let uu____13987 =
                                 let uu____13994 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____14042  ->
                                      fun uu____14043  ->
                                        match (uu____14042, uu____14043) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____14129 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____14129 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13994 in
                               (match uu____13987 with
                                | (decls2,eqns,env01) ->
                                    let uu____14169 =
                                      let isDeclFun uu___117_14177 =
                                        match uu___117_14177 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____14178 -> true
                                        | uu____14184 -> false in
                                      let uu____14185 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____14185
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____14169 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____14215 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____14215
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
        let uu____14249 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____14249 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____14252 = encode_sigelt' env se in
      match uu____14252 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____14262 =
                  let uu____14263 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____14263 in
                [uu____14262]
            | uu____14264 ->
                let uu____14265 =
                  let uu____14267 =
                    let uu____14268 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____14268 in
                  uu____14267 :: g in
                let uu____14269 =
                  let uu____14271 =
                    let uu____14272 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____14272 in
                  [uu____14271] in
                FStar_List.append uu____14265 uu____14269 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____14282 =
          let uu____14283 = FStar_Syntax_Subst.compress t in
          uu____14283.FStar_Syntax_Syntax.n in
        match uu____14282 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____14287)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____14290 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14293 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____14296 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____14298 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14300 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____14308 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____14311 =
            let uu____14312 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____14312 Prims.op_Negation in
          if uu____14311
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____14332 ->
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
               let uu____14352 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____14352 with
               | (aname,atok,env2) ->
                   let uu____14362 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____14362 with
                    | (formals,uu____14372) ->
                        let uu____14379 =
                          let uu____14382 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____14382 env2 in
                        (match uu____14379 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____14390 =
                                 let uu____14391 =
                                   let uu____14397 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____14406  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____14397,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____14391 in
                               [uu____14390;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____14413 =
                               let aux uu____14442 uu____14443 =
                                 match (uu____14442, uu____14443) with
                                 | ((bv,uu____14470),(env3,acc_sorts,acc)) ->
                                     let uu____14491 = gen_term_var env3 bv in
                                     (match uu____14491 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____14413 with
                              | (uu____14529,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____14543 =
                                      let uu____14547 =
                                        let uu____14548 =
                                          let uu____14554 =
                                            let uu____14555 =
                                              let uu____14558 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____14558) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____14555 in
                                          ([[app]], xs_sorts, uu____14554) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14548 in
                                      (uu____14547,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14543 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____14570 =
                                      let uu____14574 =
                                        let uu____14575 =
                                          let uu____14581 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____14581) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14575 in
                                      (uu____14574,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14570 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____14591 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____14591 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14607,uu____14608)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____14609 = new_term_constant_and_tok_from_lid env lid in
          (match uu____14609 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14620,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____14625 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_14628  ->
                      match uu___118_14628 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____14629 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____14632 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14633 -> false)) in
            Prims.op_Negation uu____14625 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____14639 = encode_top_level_val env fv t quals in
             match uu____14639 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____14651 =
                   let uu____14653 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14653 in
                 (uu____14651, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____14659 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____14659 with
           | (uu____14664,f1) ->
               let uu____14666 = encode_formula f1 env in
               (match uu____14666 with
                | (f2,decls) ->
                    let g =
                      let uu____14675 =
                        let uu____14676 =
                          let uu____14680 =
                            let uu____14682 =
                              let uu____14683 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____14683 in
                            FStar_Pervasives_Native.Some uu____14682 in
                          let uu____14684 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____14680, uu____14684) in
                        FStar_SMTEncoding_Util.mkAssume uu____14676 in
                      [uu____14675] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14688) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____14695 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14710 =
                       let uu____14712 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14712.FStar_Syntax_Syntax.fv_name in
                     uu____14710.FStar_Syntax_Syntax.v in
                   let uu____14713 =
                     let uu____14714 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14714 in
                   if uu____14713
                   then
                     let val_decl =
                       let uu___151_14729 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14729.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14729.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_14729.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____14733 = encode_sigelt' env1 val_decl in
                     match uu____14733 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____14695 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14750,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14752;
                          FStar_Syntax_Syntax.lbtyp = uu____14753;
                          FStar_Syntax_Syntax.lbeff = uu____14754;
                          FStar_Syntax_Syntax.lbdef = uu____14755;_}::[]),uu____14756)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____14768 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14768 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____14787 =
                   let uu____14789 =
                     let uu____14790 =
                       let uu____14794 =
                         let uu____14795 =
                           let uu____14801 =
                             let uu____14802 =
                               let uu____14805 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14805) in
                             FStar_SMTEncoding_Util.mkEq uu____14802 in
                           ([[b2t_x]], [xx], uu____14801) in
                         FStar_SMTEncoding_Util.mkForall uu____14795 in
                       (uu____14794,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14790 in
                   [uu____14789] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____14787 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14822,uu____14823) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_14829  ->
                  match uu___119_14829 with
                  | FStar_Syntax_Syntax.Discriminator uu____14830 -> true
                  | uu____14831 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14833,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14841 =
                     let uu____14842 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14842.FStar_Ident.idText in
                   uu____14841 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_14845  ->
                     match uu___120_14845 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14846 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14849) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_14859  ->
                  match uu___121_14859 with
                  | FStar_Syntax_Syntax.Projector uu____14860 -> true
                  | uu____14863 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____14866 = try_lookup_free_var env l in
          (match uu____14866 with
           | FStar_Pervasives_Native.Some uu____14870 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_14873 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_14873.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_14873.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_14873.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____14879) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14889) ->
          let uu____14894 = encode_sigelts env ses in
          (match uu____14894 with
           | (g,env1) ->
               let uu____14904 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_14918  ->
                         match uu___122_14918 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____14919;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____14920;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____14921;_}
                             -> false
                         | uu____14923 -> true)) in
               (match uu____14904 with
                | (g',inversions) ->
                    let uu____14932 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_14944  ->
                              match uu___123_14944 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14945 ->
                                  true
                              | uu____14951 -> false)) in
                    (match uu____14932 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____14962,tps,k,uu____14965,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_14976  ->
                    match uu___124_14976 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14977 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14984 = c in
              match uu____14984 with
              | (name,args,uu____14988,uu____14989,uu____14990) ->
                  let uu____14993 =
                    let uu____14994 =
                      let uu____15000 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____15011  ->
                                match uu____15011 with
                                | (uu____15015,sort,uu____15017) -> sort)) in
                      (name, uu____15000, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14994 in
                  [uu____14993]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____15035 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____15040 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____15040 FStar_Option.isNone)) in
            if uu____15035
            then []
            else
              (let uu____15057 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____15057 with
               | (xxsym,xx) ->
                   let uu____15063 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____15092  ->
                             fun l  ->
                               match uu____15092 with
                               | (out,decls) ->
                                   let uu____15104 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____15104 with
                                    | (uu____15110,data_t) ->
                                        let uu____15112 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____15112 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____15141 =
                                                 let uu____15142 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____15142.FStar_Syntax_Syntax.n in
                                               match uu____15141 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____15150,indices) ->
                                                   indices
                                               | uu____15166 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____15183  ->
                                                         match uu____15183
                                                         with
                                                         | (x,uu____15187) ->
                                                             let uu____15188
                                                               =
                                                               let uu____15189
                                                                 =
                                                                 let uu____15193
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____15193,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____15189 in
                                                             push_term_var
                                                               env1 x
                                                               uu____15188)
                                                    env) in
                                             let uu____15195 =
                                               encode_args indices env1 in
                                             (match uu____15195 with
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
                                                      let uu____15219 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____15230
                                                                 =
                                                                 let uu____15233
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____15233,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____15230)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____15219
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____15235 =
                                                      let uu____15236 =
                                                        let uu____15239 =
                                                          let uu____15240 =
                                                            let uu____15243 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____15243,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____15240 in
                                                        (out, uu____15239) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____15236 in
                                                    (uu____15235,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____15063 with
                    | (data_ax,decls) ->
                        let uu____15251 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____15251 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____15265 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____15265 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____15268 =
                                 let uu____15272 =
                                   let uu____15273 =
                                     let uu____15279 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____15287 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____15279,
                                       uu____15287) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____15273 in
                                 let uu____15295 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____15272,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____15295) in
                               FStar_SMTEncoding_Util.mkAssume uu____15268 in
                             let pattern_guarded_inversion =
                               let uu____15299 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____15299
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____15310 =
                                   let uu____15311 =
                                     let uu____15315 =
                                       let uu____15316 =
                                         let uu____15322 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____15330 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____15322, uu____15330) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____15316 in
                                     let uu____15338 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____15315,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____15338) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____15311 in
                                 [uu____15310]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____15341 =
            let uu____15349 =
              let uu____15350 = FStar_Syntax_Subst.compress k in
              uu____15350.FStar_Syntax_Syntax.n in
            match uu____15349 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____15379 -> (tps, k) in
          (match uu____15341 with
           | (formals,res) ->
               let uu____15394 = FStar_Syntax_Subst.open_term formals res in
               (match uu____15394 with
                | (formals1,res1) ->
                    let uu____15401 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____15401 with
                     | (vars,guards,env',binder_decls,uu____15416) ->
                         let uu____15423 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____15423 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____15436 =
                                  let uu____15440 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____15440) in
                                FStar_SMTEncoding_Util.mkApp uu____15436 in
                              let uu____15445 =
                                let tname_decl =
                                  let uu____15451 =
                                    let uu____15452 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____15470  ->
                                              match uu____15470 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____15478 = varops.next_id () in
                                    (tname, uu____15452,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____15478, false) in
                                  constructor_or_logic_type_decl uu____15451 in
                                let uu____15483 =
                                  match vars with
                                  | [] ->
                                      let uu____15490 =
                                        let uu____15491 =
                                          let uu____15493 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____15493 in
                                        push_free_var env1 t tname
                                          uu____15491 in
                                      ([], uu____15490)
                                  | uu____15497 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____15503 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____15503 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____15512 =
                                          let uu____15516 =
                                            let uu____15517 =
                                              let uu____15525 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____15525) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____15517 in
                                          (uu____15516,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____15512 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____15483 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____15445 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____15548 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____15548 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____15565 =
                                               let uu____15566 =
                                                 let uu____15570 =
                                                   let uu____15571 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____15571 in
                                                 (uu____15570,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15566 in
                                             [uu____15565]
                                           else [] in
                                         let uu____15574 =
                                           let uu____15576 =
                                             let uu____15578 =
                                               let uu____15579 =
                                                 let uu____15583 =
                                                   let uu____15584 =
                                                     let uu____15590 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____15590) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____15584 in
                                                 (uu____15583,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15579 in
                                             [uu____15578] in
                                           FStar_List.append karr uu____15576 in
                                         FStar_List.append decls1 uu____15574 in
                                   let aux =
                                     let uu____15599 =
                                       let uu____15601 =
                                         inversion_axioms tapp vars in
                                       let uu____15603 =
                                         let uu____15605 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____15605] in
                                       FStar_List.append uu____15601
                                         uu____15603 in
                                     FStar_List.append kindingAx uu____15599 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15610,uu____15611,uu____15612,uu____15613,uu____15614)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15619,t,uu____15621,n_tps,uu____15623) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____15628 = new_term_constant_and_tok_from_lid env d in
          (match uu____15628 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____15639 = FStar_Syntax_Util.arrow_formals t in
               (match uu____15639 with
                | (formals,t_res) ->
                    let uu____15661 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____15661 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____15670 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____15670 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____15712 =
                                            mk_term_projector_name d x in
                                          (uu____15712,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15714 =
                                  let uu____15724 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15724, true) in
                                FStar_All.pipe_right uu____15714
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
                              let uu____15746 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____15746 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15754::uu____15755 ->
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
                                         let uu____15780 =
                                           let uu____15786 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15786) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15780
                                     | uu____15799 -> tok_typing in
                                   let uu____15804 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____15804 with
                                    | (vars',guards',env'',decls_formals,uu____15819)
                                        ->
                                        let uu____15826 =
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
                                        (match uu____15826 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15845 ->
                                                   let uu____15849 =
                                                     let uu____15850 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15850 in
                                                   [uu____15849] in
                                             let encode_elim uu____15857 =
                                               let uu____15858 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____15858 with
                                               | (head1,args) ->
                                                   let uu____15887 =
                                                     let uu____15888 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____15888.FStar_Syntax_Syntax.n in
                                                   (match uu____15887 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____15895;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____15896;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____15897;_},uu____15898)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15904 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15904
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
                                                                 | uu____15933
                                                                    ->
                                                                    let uu____15934
                                                                    =
                                                                    let uu____15935
                                                                    =
                                                                    let uu____15938
                                                                    =
                                                                    let uu____15939
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15939 in
                                                                    (uu____15938,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____15935 in
                                                                    raise
                                                                    uu____15934 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15950
                                                                    =
                                                                    let uu____15951
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15951 in
                                                                    if
                                                                    uu____15950
                                                                    then
                                                                    let uu____15958
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15958]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15960
                                                               =
                                                               let uu____15967
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____16000
                                                                     ->
                                                                    fun
                                                                    uu____16001
                                                                     ->
                                                                    match 
                                                                    (uu____16000,
                                                                    uu____16001)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16052
                                                                    =
                                                                    let uu____16056
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____16056 in
                                                                    (match uu____16052
                                                                    with
                                                                    | 
                                                                    (uu____16063,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16069
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____16069
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16071
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____16071
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
                                                                 uu____15967 in
                                                             (match uu____15960
                                                              with
                                                              | (uu____16079,arg_vars,elim_eqns_or_guards,uu____16082)
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
                                                                    let uu____16101
                                                                    =
                                                                    let uu____16105
                                                                    =
                                                                    let uu____16106
                                                                    =
                                                                    let uu____16112
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16118
                                                                    =
                                                                    let uu____16119
                                                                    =
                                                                    let uu____16122
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____16122) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16119 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16112,
                                                                    uu____16118) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16106 in
                                                                    (uu____16105,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16101 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____16135
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____16135,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____16137
                                                                    =
                                                                    let uu____16141
                                                                    =
                                                                    let uu____16142
                                                                    =
                                                                    let uu____16148
                                                                    =
                                                                    let uu____16151
                                                                    =
                                                                    let uu____16153
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____16153] in
                                                                    [uu____16151] in
                                                                    let uu____16156
                                                                    =
                                                                    let uu____16157
                                                                    =
                                                                    let uu____16160
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____16161
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____16160,
                                                                    uu____16161) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16157 in
                                                                    (uu____16148,
                                                                    [x],
                                                                    uu____16156) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16142 in
                                                                    let uu____16171
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____16141,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16171) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16137
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16176
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
                                                                    (let uu____16193
                                                                    =
                                                                    let uu____16194
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____16194
                                                                    dapp1 in
                                                                    [uu____16193]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____16176
                                                                    FStar_List.flatten in
                                                                    let uu____16198
                                                                    =
                                                                    let uu____16202
                                                                    =
                                                                    let uu____16203
                                                                    =
                                                                    let uu____16209
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16215
                                                                    =
                                                                    let uu____16216
                                                                    =
                                                                    let uu____16219
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16219) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16216 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16209,
                                                                    uu____16215) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16203 in
                                                                    (uu____16202,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16198) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____16231 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____16231
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
                                                                 | uu____16260
                                                                    ->
                                                                    let uu____16261
                                                                    =
                                                                    let uu____16262
                                                                    =
                                                                    let uu____16265
                                                                    =
                                                                    let uu____16266
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16266 in
                                                                    (uu____16265,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____16262 in
                                                                    raise
                                                                    uu____16261 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16277
                                                                    =
                                                                    let uu____16278
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16278 in
                                                                    if
                                                                    uu____16277
                                                                    then
                                                                    let uu____16285
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____16285]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____16287
                                                               =
                                                               let uu____16294
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____16327
                                                                     ->
                                                                    fun
                                                                    uu____16328
                                                                     ->
                                                                    match 
                                                                    (uu____16327,
                                                                    uu____16328)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16379
                                                                    =
                                                                    let uu____16383
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____16383 in
                                                                    (match uu____16379
                                                                    with
                                                                    | 
                                                                    (uu____16390,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16396
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____16396
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16398
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____16398
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
                                                                 uu____16294 in
                                                             (match uu____16287
                                                              with
                                                              | (uu____16406,arg_vars,elim_eqns_or_guards,uu____16409)
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
                                                                    let uu____16428
                                                                    =
                                                                    let uu____16432
                                                                    =
                                                                    let uu____16433
                                                                    =
                                                                    let uu____16439
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16445
                                                                    =
                                                                    let uu____16446
                                                                    =
                                                                    let uu____16449
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____16449) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16446 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16439,
                                                                    uu____16445) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16433 in
                                                                    (uu____16432,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16428 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____16462
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____16462,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____16464
                                                                    =
                                                                    let uu____16468
                                                                    =
                                                                    let uu____16469
                                                                    =
                                                                    let uu____16475
                                                                    =
                                                                    let uu____16478
                                                                    =
                                                                    let uu____16480
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____16480] in
                                                                    [uu____16478] in
                                                                    let uu____16483
                                                                    =
                                                                    let uu____16484
                                                                    =
                                                                    let uu____16487
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____16488
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____16487,
                                                                    uu____16488) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16484 in
                                                                    (uu____16475,
                                                                    [x],
                                                                    uu____16483) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16469 in
                                                                    let uu____16498
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____16468,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16498) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16464
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16503
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
                                                                    (let uu____16520
                                                                    =
                                                                    let uu____16521
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____16521
                                                                    dapp1 in
                                                                    [uu____16520]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____16503
                                                                    FStar_List.flatten in
                                                                    let uu____16525
                                                                    =
                                                                    let uu____16529
                                                                    =
                                                                    let uu____16530
                                                                    =
                                                                    let uu____16536
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16542
                                                                    =
                                                                    let uu____16543
                                                                    =
                                                                    let uu____16546
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16546) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16543 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16536,
                                                                    uu____16542) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16530 in
                                                                    (uu____16529,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16525) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____16556 ->
                                                        ((let uu____16558 =
                                                            let uu____16559 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____16560 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____16559
                                                              uu____16560 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____16558);
                                                         ([], []))) in
                                             let uu____16563 = encode_elim () in
                                             (match uu____16563 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____16575 =
                                                      let uu____16577 =
                                                        let uu____16579 =
                                                          let uu____16581 =
                                                            let uu____16583 =
                                                              let uu____16584
                                                                =
                                                                let uu____16590
                                                                  =
                                                                  let uu____16592
                                                                    =
                                                                    let uu____16593
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16593 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____16592 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____16590) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____16584 in
                                                            [uu____16583] in
                                                          let uu____16596 =
                                                            let uu____16598 =
                                                              let uu____16600
                                                                =
                                                                let uu____16602
                                                                  =
                                                                  let uu____16604
                                                                    =
                                                                    let uu____16606
                                                                    =
                                                                    let uu____16608
                                                                    =
                                                                    let uu____16609
                                                                    =
                                                                    let uu____16613
                                                                    =
                                                                    let uu____16614
                                                                    =
                                                                    let uu____16620
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16620) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16614 in
                                                                    (uu____16613,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16609 in
                                                                    let uu____16627
                                                                    =
                                                                    let uu____16629
                                                                    =
                                                                    let uu____16630
                                                                    =
                                                                    let uu____16634
                                                                    =
                                                                    let uu____16635
                                                                    =
                                                                    let uu____16641
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____16647
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16641,
                                                                    uu____16647) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16635 in
                                                                    (uu____16634,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16630 in
                                                                    [uu____16629] in
                                                                    uu____16608
                                                                    ::
                                                                    uu____16627 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____16606 in
                                                                  FStar_List.append
                                                                    uu____16604
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____16602 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____16600 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____16598 in
                                                          FStar_List.append
                                                            uu____16581
                                                            uu____16596 in
                                                        FStar_List.append
                                                          decls3 uu____16579 in
                                                      FStar_List.append
                                                        decls2 uu____16577 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____16575 in
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
           (fun uu____16675  ->
              fun se  ->
                match uu____16675 with
                | (g,env1) ->
                    let uu____16687 = encode_sigelt env1 se in
                    (match uu____16687 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16725 =
        match uu____16725 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____16743 ->
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
                 ((let uu____16748 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____16748
                   then
                     let uu____16749 = FStar_Syntax_Print.bv_to_string x in
                     let uu____16750 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____16751 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16749 uu____16750 uu____16751
                   else ());
                  (let uu____16753 = encode_term t1 env1 in
                   match uu____16753 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____16763 =
                         let uu____16767 =
                           let uu____16768 =
                             let uu____16769 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____16769
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____16768 in
                         new_term_constant_from_string env1 x uu____16767 in
                       (match uu____16763 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____16780 = FStar_Options.log_queries () in
                              if uu____16780
                              then
                                let uu____16782 =
                                  let uu____16783 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____16784 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____16785 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16783 uu____16784 uu____16785 in
                                FStar_Pervasives_Native.Some uu____16782
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____16796,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____16805 = encode_free_var env1 fv t t_norm [] in
                 (match uu____16805 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____16818,se,uu____16820) ->
                 let uu____16823 = encode_sigelt env1 se in
                 (match uu____16823 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16833,se) ->
                 let uu____16837 = encode_sigelt env1 se in
                 (match uu____16837 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16847 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16847 with | (uu____16859,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____16911  ->
            match uu____16911 with
            | (l,uu____16918,uu____16919) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____16946  ->
            match uu____16946 with
            | (l,uu____16954,uu____16955) ->
                let uu____16960 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                    (FStar_Pervasives_Native.fst l) in
                let uu____16961 =
                  let uu____16963 =
                    let uu____16964 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____16964 in
                  [uu____16963] in
                uu____16960 :: uu____16961)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____16976 =
      let uu____16978 =
        let uu____16979 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____16981 =
          let uu____16982 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____16982 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____16979;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____16981
        } in
      [uu____16978] in
    FStar_ST.write last_env uu____16976
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____16994 = FStar_ST.read last_env in
      match uu____16994 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17000 ->
          let uu___153_17002 = e in
          let uu____17003 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_17002.bindings);
            depth = (uu___153_17002.depth);
            tcenv;
            warn = (uu___153_17002.warn);
            cache = (uu___153_17002.cache);
            nolabels = (uu___153_17002.nolabels);
            use_zfuel_name = (uu___153_17002.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_17002.encode_non_total_function_typ);
            current_module_name = uu____17003
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____17008 = FStar_ST.read last_env in
    match uu____17008 with
    | [] -> failwith "Empty env stack"
    | uu____17013::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____17022  ->
    let uu____17023 = FStar_ST.read last_env in
    match uu____17023 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_17034 = hd1 in
          {
            bindings = (uu___154_17034.bindings);
            depth = (uu___154_17034.depth);
            tcenv = (uu___154_17034.tcenv);
            warn = (uu___154_17034.warn);
            cache = refs;
            nolabels = (uu___154_17034.nolabels);
            use_zfuel_name = (uu___154_17034.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_17034.encode_non_total_function_typ);
            current_module_name = (uu___154_17034.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____17041  ->
    let uu____17042 = FStar_ST.read last_env in
    match uu____17042 with
    | [] -> failwith "Popping an empty stack"
    | uu____17047::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____17056  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____17060  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____17064  ->
    let uu____17065 = FStar_ST.read last_env in
    match uu____17065 with
    | hd1::uu____17071::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____17077 -> failwith "Impossible"
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
        | (uu____17136::uu____17137,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_17143 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_17143.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_17143.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_17143.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17144 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____17157 =
        let uu____17159 =
          let uu____17160 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____17160 in
        let uu____17161 = open_fact_db_tags env in uu____17159 :: uu____17161 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17157
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
      let uu____17178 = encode_sigelt env se in
      match uu____17178 with
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
        let uu____17205 = FStar_Options.log_queries () in
        if uu____17205
        then
          let uu____17207 =
            let uu____17208 =
              let uu____17209 =
                let uu____17210 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____17210 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____17209 in
            FStar_SMTEncoding_Term.Caption uu____17208 in
          uu____17207 :: decls
        else decls in
      let env =
        let uu____17217 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17217 tcenv in
      let uu____17218 = encode_top_level_facts env se in
      match uu____17218 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____17227 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____17227))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____17240 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____17240
       then
         let uu____17241 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____17241
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____17271  ->
                 fun se  ->
                   match uu____17271 with
                   | (g,env2) ->
                       let uu____17283 = encode_top_level_facts env2 se in
                       (match uu____17283 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____17296 =
         encode_signature
           (let uu___156_17302 = env in
            {
              bindings = (uu___156_17302.bindings);
              depth = (uu___156_17302.depth);
              tcenv = (uu___156_17302.tcenv);
              warn = false;
              cache = (uu___156_17302.cache);
              nolabels = (uu___156_17302.nolabels);
              use_zfuel_name = (uu___156_17302.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_17302.encode_non_total_function_typ);
              current_module_name = (uu___156_17302.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____17296 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____17314 = FStar_Options.log_queries () in
             if uu____17314
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_17321 = env1 in
               {
                 bindings = (uu___157_17321.bindings);
                 depth = (uu___157_17321.depth);
                 tcenv = (uu___157_17321.tcenv);
                 warn = true;
                 cache = (uu___157_17321.cache);
                 nolabels = (uu___157_17321.nolabels);
                 use_zfuel_name = (uu___157_17321.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_17321.encode_non_total_function_typ);
                 current_module_name = (uu___157_17321.current_module_name)
               });
            (let uu____17323 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____17323
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
        (let uu____17361 =
           let uu____17362 = FStar_TypeChecker_Env.current_module tcenv in
           uu____17362.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17361);
        (let env =
           let uu____17364 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____17364 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____17373 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____17394 = aux rest in
                 (match uu____17394 with
                  | (out,rest1) ->
                      let t =
                        let uu____17412 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____17412 with
                        | FStar_Pervasives_Native.Some uu____17416 ->
                            let uu____17417 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____17417
                              x.FStar_Syntax_Syntax.sort
                        | uu____17418 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____17421 =
                        let uu____17423 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_17426 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_17426.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_17426.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____17423 :: out in
                      (uu____17421, rest1))
             | uu____17429 -> ([], bindings1) in
           let uu____17433 = aux bindings in
           match uu____17433 with
           | (closing,bindings1) ->
               let uu____17447 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____17447, bindings1) in
         match uu____17373 with
         | (q1,bindings1) ->
             let uu____17460 =
               let uu____17463 =
                 FStar_List.filter
                   (fun uu___125_17467  ->
                      match uu___125_17467 with
                      | FStar_TypeChecker_Env.Binding_sig uu____17468 ->
                          false
                      | uu____17472 -> true) bindings1 in
               encode_env_bindings env uu____17463 in
             (match uu____17460 with
              | (env_decls,env1) ->
                  ((let uu____17483 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____17483
                    then
                      let uu____17484 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17484
                    else ());
                   (let uu____17486 = encode_formula q1 env1 in
                    match uu____17486 with
                    | (phi,qdecls) ->
                        let uu____17498 =
                          let uu____17501 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17501 phi in
                        (match uu____17498 with
                         | (labels,phi1) ->
                             let uu____17511 = encode_labels labels in
                             (match uu____17511 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____17532 =
                                      let uu____17536 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____17537 =
                                        varops.mk_unique "@query" in
                                      (uu____17536,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17537) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17532 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____17552 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17552 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____17554 = encode_formula q env in
       match uu____17554 with
       | (f,uu____17558) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____17560) -> true
             | uu____17563 -> false)))