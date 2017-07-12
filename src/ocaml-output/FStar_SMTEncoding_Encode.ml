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
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
        && (isInteger sz_arg.FStar_Syntax_Syntax.n)
  | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3011)::uu____3012::[]) ->
      ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid) ||
         (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_to_nat_lid))
        && (isInteger sz_arg.FStar_Syntax_Syntax.n)
  | uu____3038 -> false
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
        (let uu____3192 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3192
         then
           let uu____3193 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3193
         else ());
        (let uu____3195 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3244  ->
                   fun b  ->
                     match uu____3244 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3287 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____3296 = gen_term_var env1 x in
                           match uu____3296 with
                           | (xxsym,xx,env') ->
                               let uu____3310 =
                                 let uu____3313 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3313 env1 xx in
                               (match uu____3310 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____3287 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____3195 with
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
          let uu____3401 = encode_term t env in
          match uu____3401 with
          | (t1,decls) ->
              let uu____3408 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3408, decls)
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
          let uu____3416 = encode_term t env in
          match uu____3416 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____3425 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3425, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____3427 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3427, decls))
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
        let uu____3433 = encode_args args_e env in
        match uu____3433 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3445 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3452 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3452 in
            let binary arg_tms1 =
              let uu____3461 =
                let uu____3462 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3462 in
              let uu____3463 =
                let uu____3464 =
                  let uu____3465 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3465 in
                FStar_SMTEncoding_Term.unboxInt uu____3464 in
              (uu____3461, uu____3463) in
            let mk_default uu____3470 =
              let uu____3471 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3471 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3512 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3512
              then
                let uu____3513 = let uu____3514 = mk_args ts in op uu____3514 in
                FStar_All.pipe_right uu____3513 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3537 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3537
              then
                let uu____3538 = binary ts in
                match uu____3538 with
                | (t1,t2) ->
                    let uu____3543 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3543
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3546 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3546
                 then
                   let uu____3547 = op (binary ts) in
                   FStar_All.pipe_right uu____3547
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
            let uu____3637 =
              let uu____3643 =
                FStar_List.tryFind
                  (fun uu____3658  ->
                     match uu____3658 with
                     | (l,uu____3665) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3643 FStar_Util.must in
            (match uu____3637 with
             | (uu____3690,op) ->
                 let uu____3698 = op arg_tms in (uu____3698, decls))
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
        let uu____3705 = FStar_List.hd args_e in
        match uu____3705 with
        | (tm_sz,uu____3710) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz) in
            let sz_decls =
              let uu____3719 = FStar_Util.smap_try_find env.cache sz_key in
              match uu____3719 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz in
                  ((let uu____3725 = mk_cache_entry env "" [] [] in
                    FStar_Util.smap_add env.cache sz_key uu____3725);
                   t_decls) in
            let uu____3726 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3737::(sz_arg,uu____3739)::uu____3740::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3774 =
                    let uu____3776 = FStar_List.tail args_e in
                    FStar_List.tail uu____3776 in
                  let uu____3778 =
                    let uu____3780 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____3780 in
                  (uu____3774, uu____3778)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3784::(sz_arg,uu____3786)::uu____3787::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3821 =
                    let uu____3822 = FStar_Syntax_Print.term_to_string sz_arg in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____3822 in
                  failwith uu____3821
              | uu____3827 ->
                  let uu____3831 = FStar_List.tail args_e in
                  (uu____3831, FStar_Pervasives_Native.None) in
            (match uu____3726 with
             | (arg_tms,ext_sz) ->
                 let uu____3844 = encode_args arg_tms env in
                 (match uu____3844 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3857 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____3864 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3864 in
                      let unary_arith arg_tms2 =
                        let uu____3871 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____3871 in
                      let binary arg_tms2 =
                        let uu____3880 =
                          let uu____3881 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3881 in
                        let uu____3882 =
                          let uu____3883 =
                            let uu____3884 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____3884 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3883 in
                        (uu____3880, uu____3882) in
                      let binary_arith arg_tms2 =
                        let uu____3894 =
                          let uu____3895 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3895 in
                        let uu____3896 =
                          let uu____3897 =
                            let uu____3898 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____3898 in
                          FStar_SMTEncoding_Term.unboxInt uu____3897 in
                        (uu____3894, uu____3896) in
                      let mk_bv op mk_args resBox ts =
                        let uu____3942 =
                          let uu____3943 = mk_args ts in op uu____3943 in
                        FStar_All.pipe_right uu____3942 resBox in
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
                        let uu____4004 =
                          let uu____4007 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible" in
                          FStar_SMTEncoding_Util.mkBvUext uu____4007 in
                        let uu____4009 =
                          let uu____4012 =
                            let uu____4013 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible" in
                            sz + uu____4013 in
                          FStar_SMTEncoding_Term.boxBitVec uu____4012 in
                        mk_bv uu____4004 unary uu____4009 arg_tms2 in
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
                      let uu____4131 =
                        let uu____4137 =
                          FStar_List.tryFind
                            (fun uu____4152  ->
                               match uu____4152 with
                               | (l,uu____4159) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____4137 FStar_Util.must in
                      (match uu____4131 with
                       | (uu____4185,op) ->
                           let uu____4193 = op arg_tms1 in
                           (uu____4193, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____4201 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____4201
       then
         let uu____4202 = FStar_Syntax_Print.tag_of_term t in
         let uu____4203 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____4204 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4202 uu____4203
           uu____4204
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4208 ->
           let uu____4223 =
             let uu____4224 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4225 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4226 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4227 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4224
               uu____4225 uu____4226 uu____4227 in
           failwith uu____4223
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4230 =
             let uu____4231 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4232 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4233 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4234 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4231
               uu____4232 uu____4233 uu____4234 in
           failwith uu____4230
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4238 =
             let uu____4239 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4239 in
           failwith uu____4238
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____4244) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4274) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4283 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____4283, [])
       | FStar_Syntax_Syntax.Tm_type uu____4285 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4288) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____4294 = encode_const c in (uu____4294, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____4309 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____4309 with
            | (binders1,res) ->
                let uu____4316 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____4316
                then
                  let uu____4319 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____4319 with
                   | (vars,guards,env',decls,uu____4334) ->
                       let fsym =
                         let uu____4344 = varops.fresh "f" in
                         (uu____4344, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____4347 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_4353 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_4353.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_4353.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_4353.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_4353.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_4353.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_4353.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_4353.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_4353.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_4353.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_4353.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_4353.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_4353.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_4353.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_4353.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_4353.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_4353.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_4353.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_4353.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_4353.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_4353.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_4353.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_4353.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_4353.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_4353.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_4353.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_4353.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____4347 with
                        | (pre_opt,res_t) ->
                            let uu____4360 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____4360 with
                             | (res_pred,decls') ->
                                 let uu____4367 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4374 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____4374, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4377 =
                                         encode_formula pre env' in
                                       (match uu____4377 with
                                        | (guard,decls0) ->
                                            let uu____4385 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____4385, decls0)) in
                                 (match uu____4367 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4393 =
                                          let uu____4399 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____4399) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4393 in
                                      let cvars =
                                        let uu____4409 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____4409
                                          (FStar_List.filter
                                             (fun uu____4418  ->
                                                match uu____4418 with
                                                | (x,uu____4422) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4433 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4433 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4438 =
                                             let uu____4439 =
                                               let uu____4443 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____4443) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4439 in
                                           (uu____4438,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4454 =
                                               let uu____4455 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4455 in
                                             varops.mk_unique uu____4454 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____4462 =
                                               FStar_Options.log_queries () in
                                             if uu____4462
                                             then
                                               let uu____4464 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4464
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____4470 =
                                               let uu____4474 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____4474) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4470 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____4482 =
                                               let uu____4486 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____4486,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4482 in
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
                                             let uu____4499 =
                                               let uu____4503 =
                                                 let uu____4504 =
                                                   let uu____4510 =
                                                     let uu____4511 =
                                                       let uu____4514 =
                                                         let uu____4515 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4515 in
                                                       (f_has_t, uu____4514) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4511 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4510) in
                                                 mkForall_fuel uu____4504 in
                                               (uu____4503,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4499 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____4528 =
                                               let uu____4532 =
                                                 let uu____4533 =
                                                   let uu____4539 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4539) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____4533 in
                                               (uu____4532,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4528 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____4553 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____4553);
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
                     let uu____4564 =
                       let uu____4568 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____4568,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4564 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____4577 =
                       let uu____4581 =
                         let uu____4582 =
                           let uu____4588 =
                             let uu____4589 =
                               let uu____4592 =
                                 let uu____4593 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4593 in
                               (f_has_t, uu____4592) in
                             FStar_SMTEncoding_Util.mkImp uu____4589 in
                           ([[f_has_t]], [fsym], uu____4588) in
                         mkForall_fuel uu____4582 in
                       (uu____4581, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4577 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4607 ->
           let uu____4612 =
             let uu____4615 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____4615 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____4620;
                 FStar_Syntax_Syntax.pos = uu____4621;
                 FStar_Syntax_Syntax.vars = uu____4622;_} ->
                 let uu____4629 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____4629 with
                  | (b,f1) ->
                      let uu____4643 =
                        let uu____4644 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____4644 in
                      (uu____4643, f1))
             | uu____4649 -> failwith "impossible" in
           (match uu____4612 with
            | (x,f) ->
                let uu____4656 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4656 with
                 | (base_t,decls) ->
                     let uu____4663 = gen_term_var env x in
                     (match uu____4663 with
                      | (x1,xtm,env') ->
                          let uu____4672 = encode_formula f env' in
                          (match uu____4672 with
                           | (refinement,decls') ->
                               let uu____4679 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4679 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4690 =
                                        let uu____4692 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4696 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4692
                                          uu____4696 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4690 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4715  ->
                                              match uu____4715 with
                                              | (y,uu____4719) ->
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
                                    let uu____4738 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4738 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4743 =
                                           let uu____4744 =
                                             let uu____4748 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4748) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4744 in
                                         (uu____4743,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____4760 =
                                             let uu____4761 =
                                               let uu____4762 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4762 in
                                             Prims.strcat module_name
                                               uu____4761 in
                                           varops.mk_unique uu____4760 in
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
                                           let uu____4771 =
                                             let uu____4775 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4775) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4771 in
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
                                           let uu____4786 =
                                             let uu____4790 =
                                               let uu____4791 =
                                                 let uu____4797 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4797) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4791 in
                                             (uu____4790,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4786 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4812 =
                                             let uu____4816 =
                                               let uu____4817 =
                                                 let uu____4823 =
                                                   let uu____4824 =
                                                     let uu____4827 =
                                                       let uu____4828 =
                                                         let uu____4834 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4834) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4828 in
                                                     (uu____4827, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4824 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4823) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4817 in
                                             (uu____4816,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4812 in
                                         let t_kinding =
                                           let uu____4854 =
                                             let uu____4858 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4858,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4854 in
                                         let t_interp =
                                           let uu____4868 =
                                             let uu____4872 =
                                               let uu____4873 =
                                                 let uu____4879 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4879) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4873 in
                                             let uu____4891 =
                                               let uu____4893 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4893 in
                                             (uu____4872, uu____4891,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4868 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4898 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4898);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4919 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4919 in
           let uu____4920 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____4920 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4928 =
                    let uu____4932 =
                      let uu____4933 =
                        let uu____4934 =
                          let uu____4935 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4935 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4934 in
                      varops.mk_unique uu____4933 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4932) in
                  FStar_SMTEncoding_Util.mkAssume uu____4928 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4938 ->
           let uu____4948 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4948 with
            | (head1,args_e) ->
                let uu____4976 =
                  let uu____4984 =
                    let uu____4985 = FStar_Syntax_Subst.compress head1 in
                    uu____4985.FStar_Syntax_Syntax.n in
                  (uu____4984, args_e) in
                (match uu____4976 with
                 | uu____4995 when head_redex env head1 ->
                     let uu____5003 = whnf env t in
                     encode_term uu____5003 env
                 | uu____5004 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5016 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____5025;
                       FStar_Syntax_Syntax.pos = uu____5026;
                       FStar_Syntax_Syntax.vars = uu____5027;_},uu____5028),uu____5029::
                    (v1,uu____5031)::(v2,uu____5033)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5071 = encode_term v1 env in
                     (match uu____5071 with
                      | (v11,decls1) ->
                          let uu____5078 = encode_term v2 env in
                          (match uu____5078 with
                           | (v21,decls2) ->
                               let uu____5085 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5085,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5088::(v1,uu____5090)::(v2,uu____5092)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5126 = encode_term v1 env in
                     (match uu____5126 with
                      | (v11,decls1) ->
                          let uu____5133 = encode_term v2 env in
                          (match uu____5133 with
                           | (v21,decls2) ->
                               let uu____5140 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5140,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5142) ->
                     let e0 =
                       let uu____5154 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____5154 in
                     ((let uu____5160 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____5160
                       then
                         let uu____5161 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5161
                       else ());
                      (let e =
                         let uu____5166 =
                           let uu____5167 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____5168 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5167
                             uu____5168 in
                         uu____5166 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5177),(arg,uu____5179)::[]) -> encode_term arg env
                 | uu____5197 ->
                     let uu____5205 = encode_args args_e env in
                     (match uu____5205 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5238 = encode_term head1 env in
                            match uu____5238 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5277 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____5277 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5327  ->
                                                 fun uu____5328  ->
                                                   match (uu____5327,
                                                           uu____5328)
                                                   with
                                                   | ((bv,uu____5342),
                                                      (a,uu____5344)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____5358 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____5358
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____5363 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____5363 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____5373 =
                                                   let uu____5377 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____5382 =
                                                     let uu____5383 =
                                                       let uu____5384 =
                                                         let uu____5385 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____5385 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5384 in
                                                     varops.mk_unique
                                                       uu____5383 in
                                                   (uu____5377,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5382) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5373 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____5396 = lookup_free_var_sym env fv in
                            match uu____5396 with
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
                                   FStar_Syntax_Syntax.tk = uu____5417;
                                   FStar_Syntax_Syntax.pos = uu____5418;
                                   FStar_Syntax_Syntax.vars = uu____5419;_},uu____5420)
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
                                   FStar_Syntax_Syntax.tk = uu____5431;
                                   FStar_Syntax_Syntax.pos = uu____5432;
                                   FStar_Syntax_Syntax.vars = uu____5433;_},uu____5434)
                                ->
                                let uu____5439 =
                                  let uu____5440 =
                                    let uu____5443 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5443
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5440
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5439
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5459 =
                                  let uu____5460 =
                                    let uu____5463 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5463
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5460
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5459
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5478,(FStar_Util.Inl t1,uu____5480),uu____5481)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5519,(FStar_Util.Inr c,uu____5521),uu____5522)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5560 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5580 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5580 in
                               let uu____5581 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____5581 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____5591;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5592;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5593;_},uu____5594)
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
                                     | uu____5620 ->
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
           let uu____5660 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____5660 with
            | (bs1,body1,opening) ->
                let fallback uu____5675 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____5680 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____5680, [decl]) in
                let is_impure rc =
                  let uu____5686 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____5686 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5695 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5695
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____5708 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____5708
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____5711 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____5711)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5716 =
                         let uu____5717 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5717 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5716);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____5719 =
                       (is_impure rc) &&
                         (let uu____5721 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____5721) in
                     if uu____5719
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5726 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____5726 with
                        | (vars,guards,envbody,decls,uu____5741) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____5749 = encode_term body2 envbody in
                            (match uu____5749 with
                             | (body3,decls') ->
                                 let uu____5756 =
                                   let uu____5761 = codomain_eff rc in
                                   match uu____5761 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____5773 = encode_term tfun env in
                                       (match uu____5773 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____5756 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5792 =
                                          let uu____5798 =
                                            let uu____5799 =
                                              let uu____5802 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____5802, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5799 in
                                          ([], vars, uu____5798) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5792 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____5810 =
                                              let uu____5812 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____5812
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5810 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____5823 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____5823 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5828 =
                                             let uu____5829 =
                                               let uu____5833 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5833) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5829 in
                                           (uu____5828,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5839 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____5839 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5846 =
                                                    let uu____5847 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____5847 = cache_size in
                                                  if uu____5846
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
                                                    let uu____5858 =
                                                      let uu____5859 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5859 in
                                                    varops.mk_unique
                                                      uu____5858 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____5864 =
                                                    let uu____5868 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____5868) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5864 in
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
                                                      let uu____5880 =
                                                        let uu____5881 =
                                                          let uu____5885 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____5885,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5881 in
                                                      [uu____5880] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____5893 =
                                                    let uu____5897 =
                                                      let uu____5898 =
                                                        let uu____5904 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5904) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5898 in
                                                    (uu____5897,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5893 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____5914 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5914);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5916,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5917;
                          FStar_Syntax_Syntax.lbunivs = uu____5918;
                          FStar_Syntax_Syntax.lbtyp = uu____5919;
                          FStar_Syntax_Syntax.lbeff = uu____5920;
                          FStar_Syntax_Syntax.lbdef = uu____5921;_}::uu____5922),uu____5923)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5941;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5943;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5959 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____5972 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5972, [decl_e])))
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
              let uu____6012 = encode_term e1 env in
              match uu____6012 with
              | (ee1,decls1) ->
                  let uu____6019 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____6019 with
                   | (xs,e21) ->
                       let uu____6033 = FStar_List.hd xs in
                       (match uu____6033 with
                        | (x1,uu____6041) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____6043 = encode_body e21 env' in
                            (match uu____6043 with
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
            let uu____6065 =
              let uu____6069 =
                let uu____6070 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____6070 in
              gen_term_var env uu____6069 in
            match uu____6065 with
            | (scrsym,scr',env1) ->
                let uu____6080 = encode_term e env1 in
                (match uu____6080 with
                 | (scr,decls) ->
                     let uu____6087 =
                       let encode_branch b uu____6103 =
                         match uu____6103 with
                         | (else_case,decls1) ->
                             let uu____6114 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____6114 with
                              | (p,w,br) ->
                                  let uu____6133 = encode_pat env1 p in
                                  (match uu____6133 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____6157  ->
                                                   match uu____6157 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____6162 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6177 =
                                               encode_term w1 env2 in
                                             (match uu____6177 with
                                              | (w2,decls2) ->
                                                  let uu____6185 =
                                                    let uu____6186 =
                                                      let uu____6189 =
                                                        let uu____6190 =
                                                          let uu____6193 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____6193) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6190 in
                                                      (guard, uu____6189) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6186 in
                                                  (uu____6185, decls2)) in
                                       (match uu____6162 with
                                        | (guard1,decls2) ->
                                            let uu____6201 =
                                              encode_br br env2 in
                                            (match uu____6201 with
                                             | (br1,decls3) ->
                                                 let uu____6209 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____6209,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____6087 with
                      | (match_tm,decls1) ->
                          let uu____6220 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____6220, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____6242 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____6242
       then
         let uu____6243 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6243
       else ());
      (let uu____6245 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____6245 with
       | (vars,pat_term) ->
           let uu____6255 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____6286  ->
                     fun v1  ->
                       match uu____6286 with
                       | (env1,vars1) ->
                           let uu____6314 = gen_term_var env1 v1 in
                           (match uu____6314 with
                            | (xx,uu____6326,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____6255 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____6371 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____6372 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____6373 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____6379 =
                        let uu____6382 = encode_const c in
                        (scrutinee, uu____6382) in
                      FStar_SMTEncoding_Util.mkEq uu____6379
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____6395 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____6395 with
                        | (uu____6399,uu____6400::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____6402 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6423  ->
                                  match uu____6423 with
                                  | (arg,uu____6428) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____6432 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____6432)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____6450) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____6469 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____6482 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6508  ->
                                  match uu____6508 with
                                  | (arg,uu____6516) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____6520 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____6520)) in
                      FStar_All.pipe_right uu____6482 FStar_List.flatten in
                let pat_term1 uu____6536 = encode_term pat_term env1 in
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
      let uu____6543 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____6567  ->
                fun uu____6568  ->
                  match (uu____6567, uu____6568) with
                  | ((tms,decls),(t,uu____6588)) ->
                      let uu____6599 = encode_term t env in
                      (match uu____6599 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____6543 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____6633 = FStar_Syntax_Util.list_elements e in
        match uu____6633 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____6648 =
          let uu____6658 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____6658 FStar_Syntax_Util.head_and_args in
        match uu____6648 with
        | (head1,args) ->
            let uu____6686 =
              let uu____6694 =
                let uu____6695 = FStar_Syntax_Util.un_uinst head1 in
                uu____6695.FStar_Syntax_Syntax.n in
              (uu____6694, args) in
            (match uu____6686 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6706,uu____6707)::(e,uu____6709)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____6735 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6762 =
            let uu____6772 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6772 FStar_Syntax_Util.head_and_args in
          match uu____6762 with
          | (head1,args) ->
              let uu____6801 =
                let uu____6809 =
                  let uu____6810 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6810.FStar_Syntax_Syntax.n in
                (uu____6809, args) in
              (match uu____6801 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6823)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____6843 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____6858 = smt_pat_or1 t1 in
            (match uu____6858 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____6871 = list_elements1 e in
                 FStar_All.pipe_right uu____6871
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6884 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6884
                           (FStar_List.map one_pat)))
             | uu____6892 ->
                 let uu____6896 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6896])
        | uu____6912 ->
            let uu____6914 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6914] in
      let uu____6930 =
        let uu____6943 =
          let uu____6944 = FStar_Syntax_Subst.compress t in
          uu____6944.FStar_Syntax_Syntax.n in
        match uu____6943 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6971 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6971 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____7000;
                        FStar_Syntax_Syntax.effect_name = uu____7001;
                        FStar_Syntax_Syntax.result_typ = uu____7002;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____7004)::(post,uu____7006)::(pats,uu____7008)::[];
                        FStar_Syntax_Syntax.flags = uu____7009;_}
                      ->
                      let uu____7041 = lemma_pats pats in
                      (binders1, pre, post, uu____7041)
                  | uu____7054 -> failwith "impos"))
        | uu____7067 -> failwith "Impos" in
      match uu____6930 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_7103 = env in
            {
              bindings = (uu___136_7103.bindings);
              depth = (uu___136_7103.depth);
              tcenv = (uu___136_7103.tcenv);
              warn = (uu___136_7103.warn);
              cache = (uu___136_7103.cache);
              nolabels = (uu___136_7103.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_7103.encode_non_total_function_typ);
              current_module_name = (uu___136_7103.current_module_name)
            } in
          let uu____7104 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____7104 with
           | (vars,guards,env2,decls,uu____7119) ->
               let uu____7126 =
                 let uu____7133 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____7159 =
                             let uu____7164 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____7164 FStar_List.unzip in
                           match uu____7159 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____7133 FStar_List.unzip in
               (match uu____7126 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_7223 = env2 in
                      {
                        bindings = (uu___137_7223.bindings);
                        depth = (uu___137_7223.depth);
                        tcenv = (uu___137_7223.tcenv);
                        warn = (uu___137_7223.warn);
                        cache = (uu___137_7223.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_7223.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_7223.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_7223.current_module_name)
                      } in
                    let uu____7224 =
                      let uu____7227 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____7227 env3 in
                    (match uu____7224 with
                     | (pre1,decls'') ->
                         let uu____7232 =
                           let uu____7235 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____7235 env3 in
                         (match uu____7232 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____7242 =
                                let uu____7243 =
                                  let uu____7249 =
                                    let uu____7250 =
                                      let uu____7253 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____7253, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____7250 in
                                  (pats, vars, uu____7249) in
                                FStar_SMTEncoding_Util.mkForall uu____7243 in
                              (uu____7242, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____7266 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____7266
        then
          let uu____7267 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____7268 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____7267 uu____7268
        else () in
      let enc f r l =
        let uu____7295 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____7313 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____7313 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____7295 with
        | (decls,args) ->
            let uu____7330 =
              let uu___138_7331 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_7331.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_7331.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____7330, decls) in
      let const_op f r uu____7356 = let uu____7365 = f r in (uu____7365, []) in
      let un_op f l =
        let uu____7381 = FStar_List.hd l in FStar_All.pipe_left f uu____7381 in
      let bin_op f uu___112_7394 =
        match uu___112_7394 with
        | t1::t2::[] -> f (t1, t2)
        | uu____7402 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____7429 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____7445  ->
                 match uu____7445 with
                 | (t,uu____7453) ->
                     let uu____7454 = encode_formula t env in
                     (match uu____7454 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____7429 with
        | (decls,phis) ->
            let uu____7471 =
              let uu___139_7472 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_7472.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_7472.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____7471, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____7515  ->
               match uu____7515 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____7529) -> false
                    | uu____7530 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____7543 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____7543
        else
          (let uu____7558 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____7558 r rf) in
      let mk_imp1 r uu___113_7577 =
        match uu___113_7577 with
        | (lhs,uu____7581)::(rhs,uu____7583)::[] ->
            let uu____7604 = encode_formula rhs env in
            (match uu____7604 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____7613) ->
                      (l1, decls1)
                  | uu____7616 ->
                      let uu____7617 = encode_formula lhs env in
                      (match uu____7617 with
                       | (l2,decls2) ->
                           let uu____7624 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____7624, (FStar_List.append decls1 decls2)))))
        | uu____7626 -> failwith "impossible" in
      let mk_ite r uu___114_7641 =
        match uu___114_7641 with
        | (guard,uu____7645)::(_then,uu____7647)::(_else,uu____7649)::[] ->
            let uu____7678 = encode_formula guard env in
            (match uu____7678 with
             | (g,decls1) ->
                 let uu____7685 = encode_formula _then env in
                 (match uu____7685 with
                  | (t,decls2) ->
                      let uu____7692 = encode_formula _else env in
                      (match uu____7692 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7701 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7720 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7720 in
      let connectives =
        let uu____7732 =
          let uu____7741 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____7741) in
        let uu____7754 =
          let uu____7764 =
            let uu____7773 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____7773) in
          let uu____7786 =
            let uu____7796 =
              let uu____7806 =
                let uu____7815 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____7815) in
              let uu____7828 =
                let uu____7838 =
                  let uu____7848 =
                    let uu____7857 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____7857) in
                  [uu____7848;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____7838 in
              uu____7806 :: uu____7828 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____7796 in
          uu____7764 :: uu____7786 in
        uu____7732 :: uu____7754 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____8073 = encode_formula phi' env in
            (match uu____8073 with
             | (phi2,decls) ->
                 let uu____8080 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____8080, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____8081 ->
            let uu____8086 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____8086 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____8113 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____8113 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____8121;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____8123;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____8139 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____8139 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8171::(x,uu____8173)::(t,uu____8175)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8209 = encode_term x env in
                 (match uu____8209 with
                  | (x1,decls) ->
                      let uu____8216 = encode_term t env in
                      (match uu____8216 with
                       | (t1,decls') ->
                           let uu____8223 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____8223, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____8227)::(msg,uu____8229)::(phi2,uu____8231)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____8265 =
                   let uu____8268 =
                     let uu____8269 = FStar_Syntax_Subst.compress r in
                     uu____8269.FStar_Syntax_Syntax.n in
                   let uu____8272 =
                     let uu____8273 = FStar_Syntax_Subst.compress msg in
                     uu____8273.FStar_Syntax_Syntax.n in
                   (uu____8268, uu____8272) in
                 (match uu____8265 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____8280))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____8292 -> fallback phi2)
             | uu____8295 when head_redex env head2 ->
                 let uu____8303 = whnf env phi1 in
                 encode_formula uu____8303 env
             | uu____8304 ->
                 let uu____8312 = encode_term phi1 env in
                 (match uu____8312 with
                  | (tt,decls) ->
                      let uu____8319 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_8322 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_8322.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_8322.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____8319, decls)))
        | uu____8325 ->
            let uu____8326 = encode_term phi1 env in
            (match uu____8326 with
             | (tt,decls) ->
                 let uu____8333 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_8336 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_8336.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_8336.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____8333, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____8363 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____8363 with
        | (vars,guards,env2,decls,uu____8385) ->
            let uu____8392 =
              let uu____8399 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____8426 =
                          let uu____8431 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____8448  ->
                                    match uu____8448 with
                                    | (t,uu____8454) ->
                                        encode_term t
                                          (let uu___142_8456 = env2 in
                                           {
                                             bindings =
                                               (uu___142_8456.bindings);
                                             depth = (uu___142_8456.depth);
                                             tcenv = (uu___142_8456.tcenv);
                                             warn = (uu___142_8456.warn);
                                             cache = (uu___142_8456.cache);
                                             nolabels =
                                               (uu___142_8456.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_8456.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_8456.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____8431 FStar_List.unzip in
                        match uu____8426 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____8399 FStar_List.unzip in
            (match uu____8392 with
             | (pats,decls') ->
                 let uu____8508 = encode_formula body env2 in
                 (match uu____8508 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____8527;
                             FStar_SMTEncoding_Term.rng = uu____8528;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____8536 -> guards in
                      let uu____8539 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____8539, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____8576  ->
                   match uu____8576 with
                   | (x,uu____8580) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____8586 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____8595 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____8595) uu____8586 tl1 in
             let uu____8597 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____8613  ->
                       match uu____8613 with
                       | (b,uu____8617) ->
                           let uu____8618 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____8618)) in
             (match uu____8597 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____8622) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____8634 =
                    let uu____8635 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____8635 in
                  FStar_Errors.warn pos uu____8634) in
       let uu____8636 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____8636 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____8642 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____8681  ->
                     match uu____8681 with
                     | (l,uu____8691) -> FStar_Ident.lid_equals op l)) in
           (match uu____8642 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____8714,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8743 = encode_q_body env vars pats body in
             match uu____8743 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8769 =
                     let uu____8775 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8775) in
                   FStar_SMTEncoding_Term.mkForall uu____8769
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8787 = encode_q_body env vars pats body in
             match uu____8787 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8812 =
                   let uu____8813 =
                     let uu____8819 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8819) in
                   FStar_SMTEncoding_Term.mkExists uu____8813
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8812, decls))))
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
  let uu____8898 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8898 with
  | (asym,a) ->
      let uu____8903 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8903 with
       | (xsym,x) ->
           let uu____8908 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8908 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8938 =
                      let uu____8944 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____8944, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8938 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____8959 =
                      let uu____8963 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8963) in
                    FStar_SMTEncoding_Util.mkApp uu____8959 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8971 =
                    let uu____8973 =
                      let uu____8975 =
                        let uu____8977 =
                          let uu____8978 =
                            let uu____8982 =
                              let uu____8983 =
                                let uu____8989 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8989) in
                              FStar_SMTEncoding_Util.mkForall uu____8983 in
                            (uu____8982, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8978 in
                        let uu____8998 =
                          let uu____9000 =
                            let uu____9001 =
                              let uu____9005 =
                                let uu____9006 =
                                  let uu____9012 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____9012) in
                                FStar_SMTEncoding_Util.mkForall uu____9006 in
                              (uu____9005,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____9001 in
                          [uu____9000] in
                        uu____8977 :: uu____8998 in
                      xtok_decl :: uu____8975 in
                    xname_decl :: uu____8973 in
                  (xtok1, uu____8971) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____9061 =
                    let uu____9069 =
                      let uu____9075 =
                        let uu____9076 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____9076 in
                      quant axy uu____9075 in
                    (FStar_Parser_Const.op_Eq, uu____9069) in
                  let uu____9082 =
                    let uu____9091 =
                      let uu____9099 =
                        let uu____9105 =
                          let uu____9106 =
                            let uu____9107 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____9107 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____9106 in
                        quant axy uu____9105 in
                      (FStar_Parser_Const.op_notEq, uu____9099) in
                    let uu____9113 =
                      let uu____9122 =
                        let uu____9130 =
                          let uu____9136 =
                            let uu____9137 =
                              let uu____9138 =
                                let uu____9141 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9142 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____9141, uu____9142) in
                              FStar_SMTEncoding_Util.mkLT uu____9138 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____9137 in
                          quant xy uu____9136 in
                        (FStar_Parser_Const.op_LT, uu____9130) in
                      let uu____9148 =
                        let uu____9157 =
                          let uu____9165 =
                            let uu____9171 =
                              let uu____9172 =
                                let uu____9173 =
                                  let uu____9176 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____9177 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____9176, uu____9177) in
                                FStar_SMTEncoding_Util.mkLTE uu____9173 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____9172 in
                            quant xy uu____9171 in
                          (FStar_Parser_Const.op_LTE, uu____9165) in
                        let uu____9183 =
                          let uu____9192 =
                            let uu____9200 =
                              let uu____9206 =
                                let uu____9207 =
                                  let uu____9208 =
                                    let uu____9211 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____9212 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____9211, uu____9212) in
                                  FStar_SMTEncoding_Util.mkGT uu____9208 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____9207 in
                              quant xy uu____9206 in
                            (FStar_Parser_Const.op_GT, uu____9200) in
                          let uu____9218 =
                            let uu____9227 =
                              let uu____9235 =
                                let uu____9241 =
                                  let uu____9242 =
                                    let uu____9243 =
                                      let uu____9246 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____9247 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____9246, uu____9247) in
                                    FStar_SMTEncoding_Util.mkGTE uu____9243 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____9242 in
                                quant xy uu____9241 in
                              (FStar_Parser_Const.op_GTE, uu____9235) in
                            let uu____9253 =
                              let uu____9262 =
                                let uu____9270 =
                                  let uu____9276 =
                                    let uu____9277 =
                                      let uu____9278 =
                                        let uu____9281 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____9282 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____9281, uu____9282) in
                                      FStar_SMTEncoding_Util.mkSub uu____9278 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____9277 in
                                  quant xy uu____9276 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____9270) in
                              let uu____9288 =
                                let uu____9297 =
                                  let uu____9305 =
                                    let uu____9311 =
                                      let uu____9312 =
                                        let uu____9313 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____9313 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____9312 in
                                    quant qx uu____9311 in
                                  (FStar_Parser_Const.op_Minus, uu____9305) in
                                let uu____9319 =
                                  let uu____9328 =
                                    let uu____9336 =
                                      let uu____9342 =
                                        let uu____9343 =
                                          let uu____9344 =
                                            let uu____9347 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____9348 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____9347, uu____9348) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____9344 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____9343 in
                                      quant xy uu____9342 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____9336) in
                                  let uu____9354 =
                                    let uu____9363 =
                                      let uu____9371 =
                                        let uu____9377 =
                                          let uu____9378 =
                                            let uu____9379 =
                                              let uu____9382 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____9383 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____9382, uu____9383) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____9379 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____9378 in
                                        quant xy uu____9377 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____9371) in
                                    let uu____9389 =
                                      let uu____9398 =
                                        let uu____9406 =
                                          let uu____9412 =
                                            let uu____9413 =
                                              let uu____9414 =
                                                let uu____9417 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____9418 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____9417, uu____9418) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____9414 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____9413 in
                                          quant xy uu____9412 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____9406) in
                                      let uu____9424 =
                                        let uu____9433 =
                                          let uu____9441 =
                                            let uu____9447 =
                                              let uu____9448 =
                                                let uu____9449 =
                                                  let uu____9452 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____9453 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____9452, uu____9453) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____9449 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____9448 in
                                            quant xy uu____9447 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____9441) in
                                        let uu____9459 =
                                          let uu____9468 =
                                            let uu____9476 =
                                              let uu____9482 =
                                                let uu____9483 =
                                                  let uu____9484 =
                                                    let uu____9487 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____9488 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____9487, uu____9488) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____9484 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____9483 in
                                              quant xy uu____9482 in
                                            (FStar_Parser_Const.op_And,
                                              uu____9476) in
                                          let uu____9494 =
                                            let uu____9503 =
                                              let uu____9511 =
                                                let uu____9517 =
                                                  let uu____9518 =
                                                    let uu____9519 =
                                                      let uu____9522 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____9523 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____9522,
                                                        uu____9523) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____9519 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____9518 in
                                                quant xy uu____9517 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____9511) in
                                            let uu____9529 =
                                              let uu____9538 =
                                                let uu____9546 =
                                                  let uu____9552 =
                                                    let uu____9553 =
                                                      let uu____9554 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____9554 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____9553 in
                                                  quant qx uu____9552 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____9546) in
                                              [uu____9538] in
                                            uu____9503 :: uu____9529 in
                                          uu____9468 :: uu____9494 in
                                        uu____9433 :: uu____9459 in
                                      uu____9398 :: uu____9424 in
                                    uu____9363 :: uu____9389 in
                                  uu____9328 :: uu____9354 in
                                uu____9297 :: uu____9319 in
                              uu____9262 :: uu____9288 in
                            uu____9227 :: uu____9253 in
                          uu____9192 :: uu____9218 in
                        uu____9157 :: uu____9183 in
                      uu____9122 :: uu____9148 in
                    uu____9091 :: uu____9113 in
                  uu____9061 :: uu____9082 in
                let mk1 l v1 =
                  let uu____9682 =
                    let uu____9687 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9722  ->
                              match uu____9722 with
                              | (l',uu____9731) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____9687
                      (FStar_Option.map
                         (fun uu____9767  ->
                            match uu____9767 with | (uu____9778,b) -> b v1)) in
                  FStar_All.pipe_right uu____9682 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9822  ->
                          match uu____9822 with
                          | (l',uu____9831) -> FStar_Ident.lid_equals l l')) in
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
        let uu____9860 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9860 with
        | (xxsym,xx) ->
            let uu____9865 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9865 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____9873 =
                   let uu____9877 =
                     let uu____9878 =
                       let uu____9884 =
                         let uu____9885 =
                           let uu____9888 =
                             let uu____9889 =
                               let uu____9892 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9892) in
                             FStar_SMTEncoding_Util.mkEq uu____9889 in
                           (xx_has_type, uu____9888) in
                         FStar_SMTEncoding_Util.mkImp uu____9885 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9884) in
                     FStar_SMTEncoding_Util.mkForall uu____9878 in
                   let uu____9905 =
                     let uu____9906 =
                       let uu____9907 =
                         let uu____9908 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9908 in
                       Prims.strcat module_name uu____9907 in
                     varops.mk_unique uu____9906 in
                   (uu____9877, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____9905) in
                 FStar_SMTEncoding_Util.mkAssume uu____9873)
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
    let uu____9942 =
      let uu____9943 =
        let uu____9947 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9947, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9943 in
    let uu____9949 =
      let uu____9951 =
        let uu____9952 =
          let uu____9956 =
            let uu____9957 =
              let uu____9963 =
                let uu____9964 =
                  let uu____9967 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9967) in
                FStar_SMTEncoding_Util.mkImp uu____9964 in
              ([[typing_pred]], [xx], uu____9963) in
            mkForall_fuel uu____9957 in
          (uu____9956, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9952 in
      [uu____9951] in
    uu____9942 :: uu____9949 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9995 =
      let uu____9996 =
        let uu____10000 =
          let uu____10001 =
            let uu____10007 =
              let uu____10010 =
                let uu____10012 = FStar_SMTEncoding_Term.boxBool b in
                [uu____10012] in
              [uu____10010] in
            let uu____10015 =
              let uu____10016 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____10016 tt in
            (uu____10007, [bb], uu____10015) in
          FStar_SMTEncoding_Util.mkForall uu____10001 in
        (uu____10000, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9996 in
    let uu____10027 =
      let uu____10029 =
        let uu____10030 =
          let uu____10034 =
            let uu____10035 =
              let uu____10041 =
                let uu____10042 =
                  let uu____10045 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____10045) in
                FStar_SMTEncoding_Util.mkImp uu____10042 in
              ([[typing_pred]], [xx], uu____10041) in
            mkForall_fuel uu____10035 in
          (uu____10034, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____10030 in
      [uu____10029] in
    uu____9995 :: uu____10027 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____10079 =
        let uu____10080 =
          let uu____10084 =
            let uu____10086 =
              let uu____10088 =
                let uu____10090 = FStar_SMTEncoding_Term.boxInt a in
                let uu____10091 =
                  let uu____10093 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____10093] in
                uu____10090 :: uu____10091 in
              tt :: uu____10088 in
            tt :: uu____10086 in
          ("Prims.Precedes", uu____10084) in
        FStar_SMTEncoding_Util.mkApp uu____10080 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____10079 in
    let precedes_y_x =
      let uu____10096 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____10096 in
    let uu____10098 =
      let uu____10099 =
        let uu____10103 =
          let uu____10104 =
            let uu____10110 =
              let uu____10113 =
                let uu____10115 = FStar_SMTEncoding_Term.boxInt b in
                [uu____10115] in
              [uu____10113] in
            let uu____10118 =
              let uu____10119 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____10119 tt in
            (uu____10110, [bb], uu____10118) in
          FStar_SMTEncoding_Util.mkForall uu____10104 in
        (uu____10103, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____10099 in
    let uu____10130 =
      let uu____10132 =
        let uu____10133 =
          let uu____10137 =
            let uu____10138 =
              let uu____10144 =
                let uu____10145 =
                  let uu____10148 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____10148) in
                FStar_SMTEncoding_Util.mkImp uu____10145 in
              ([[typing_pred]], [xx], uu____10144) in
            mkForall_fuel uu____10138 in
          (uu____10137, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____10133 in
      let uu____10161 =
        let uu____10163 =
          let uu____10164 =
            let uu____10168 =
              let uu____10169 =
                let uu____10175 =
                  let uu____10176 =
                    let uu____10179 =
                      let uu____10180 =
                        let uu____10182 =
                          let uu____10184 =
                            let uu____10186 =
                              let uu____10187 =
                                let uu____10190 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____10191 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____10190, uu____10191) in
                              FStar_SMTEncoding_Util.mkGT uu____10187 in
                            let uu____10192 =
                              let uu____10194 =
                                let uu____10195 =
                                  let uu____10198 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____10199 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____10198, uu____10199) in
                                FStar_SMTEncoding_Util.mkGTE uu____10195 in
                              let uu____10200 =
                                let uu____10202 =
                                  let uu____10203 =
                                    let uu____10206 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____10207 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____10206, uu____10207) in
                                  FStar_SMTEncoding_Util.mkLT uu____10203 in
                                [uu____10202] in
                              uu____10194 :: uu____10200 in
                            uu____10186 :: uu____10192 in
                          typing_pred_y :: uu____10184 in
                        typing_pred :: uu____10182 in
                      FStar_SMTEncoding_Util.mk_and_l uu____10180 in
                    (uu____10179, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____10176 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____10175) in
              mkForall_fuel uu____10169 in
            (uu____10168,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____10164 in
        [uu____10163] in
      uu____10132 :: uu____10161 in
    uu____10098 :: uu____10130 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____10237 =
      let uu____10238 =
        let uu____10242 =
          let uu____10243 =
            let uu____10249 =
              let uu____10252 =
                let uu____10254 = FStar_SMTEncoding_Term.boxString b in
                [uu____10254] in
              [uu____10252] in
            let uu____10257 =
              let uu____10258 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____10258 tt in
            (uu____10249, [bb], uu____10257) in
          FStar_SMTEncoding_Util.mkForall uu____10243 in
        (uu____10242, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____10238 in
    let uu____10269 =
      let uu____10271 =
        let uu____10272 =
          let uu____10276 =
            let uu____10277 =
              let uu____10283 =
                let uu____10284 =
                  let uu____10287 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____10287) in
                FStar_SMTEncoding_Util.mkImp uu____10284 in
              ([[typing_pred]], [xx], uu____10283) in
            mkForall_fuel uu____10277 in
          (uu____10276, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____10272 in
      [uu____10271] in
    uu____10237 :: uu____10269 in
  let mk_ref1 env reft_name uu____10309 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____10320 =
        let uu____10324 =
          let uu____10326 = FStar_SMTEncoding_Util.mkFreeV aa in
          [uu____10326] in
        (reft_name, uu____10324) in
      FStar_SMTEncoding_Util.mkApp uu____10320 in
    let refb =
      let uu____10329 =
        let uu____10333 =
          let uu____10335 = FStar_SMTEncoding_Util.mkFreeV bb in
          [uu____10335] in
        (reft_name, uu____10333) in
      FStar_SMTEncoding_Util.mkApp uu____10329 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____10339 =
      let uu____10340 =
        let uu____10344 =
          let uu____10345 =
            let uu____10351 =
              let uu____10352 =
                let uu____10355 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____10355) in
              FStar_SMTEncoding_Util.mkImp uu____10352 in
            ([[typing_pred]], [xx; aa], uu____10351) in
          mkForall_fuel uu____10345 in
        (uu____10344, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____10340 in
    [uu____10339] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____10395 =
      let uu____10396 =
        let uu____10400 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____10400, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10396 in
    [uu____10395] in
  let mk_and_interp env conj uu____10411 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10428 =
      let uu____10429 =
        let uu____10433 =
          let uu____10434 =
            let uu____10440 =
              let uu____10441 =
                let uu____10444 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____10444, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10441 in
            ([[l_and_a_b]], [aa; bb], uu____10440) in
          FStar_SMTEncoding_Util.mkForall uu____10434 in
        (uu____10433, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10429 in
    [uu____10428] in
  let mk_or_interp env disj uu____10468 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10485 =
      let uu____10486 =
        let uu____10490 =
          let uu____10491 =
            let uu____10497 =
              let uu____10498 =
                let uu____10501 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____10501, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10498 in
            ([[l_or_a_b]], [aa; bb], uu____10497) in
          FStar_SMTEncoding_Util.mkForall uu____10491 in
        (uu____10490, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10486 in
    [uu____10485] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____10542 =
      let uu____10543 =
        let uu____10547 =
          let uu____10548 =
            let uu____10554 =
              let uu____10555 =
                let uu____10558 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10558, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10555 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____10554) in
          FStar_SMTEncoding_Util.mkForall uu____10548 in
        (uu____10547, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10543 in
    [uu____10542] in
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
    let uu____10605 =
      let uu____10606 =
        let uu____10610 =
          let uu____10611 =
            let uu____10617 =
              let uu____10618 =
                let uu____10621 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10621, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10618 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____10617) in
          FStar_SMTEncoding_Util.mkForall uu____10611 in
        (uu____10610, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10606 in
    [uu____10605] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10666 =
      let uu____10667 =
        let uu____10671 =
          let uu____10672 =
            let uu____10678 =
              let uu____10679 =
                let uu____10682 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____10682, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10679 in
            ([[l_imp_a_b]], [aa; bb], uu____10678) in
          FStar_SMTEncoding_Util.mkForall uu____10672 in
        (uu____10671, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10667 in
    [uu____10666] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10723 =
      let uu____10724 =
        let uu____10728 =
          let uu____10729 =
            let uu____10735 =
              let uu____10736 =
                let uu____10739 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10739, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10736 in
            ([[l_iff_a_b]], [aa; bb], uu____10735) in
          FStar_SMTEncoding_Util.mkForall uu____10729 in
        (uu____10728, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10724 in
    [uu____10723] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____10773 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10773 in
    let uu____10775 =
      let uu____10776 =
        let uu____10780 =
          let uu____10781 =
            let uu____10787 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10787) in
          FStar_SMTEncoding_Util.mkForall uu____10781 in
        (uu____10780, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10776 in
    [uu____10775] in
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
      let uu____10827 =
        let uu____10831 =
          let uu____10833 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10833] in
        ("Valid", uu____10831) in
      FStar_SMTEncoding_Util.mkApp uu____10827 in
    let uu____10835 =
      let uu____10836 =
        let uu____10840 =
          let uu____10841 =
            let uu____10847 =
              let uu____10848 =
                let uu____10851 =
                  let uu____10852 =
                    let uu____10858 =
                      let uu____10861 =
                        let uu____10863 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10863] in
                      [uu____10861] in
                    let uu____10866 =
                      let uu____10867 =
                        let uu____10870 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10870, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10867 in
                    (uu____10858, [xx1], uu____10866) in
                  FStar_SMTEncoding_Util.mkForall uu____10852 in
                (uu____10851, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10848 in
            ([[l_forall_a_b]], [aa; bb], uu____10847) in
          FStar_SMTEncoding_Util.mkForall uu____10841 in
        (uu____10840, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10836 in
    [uu____10835] in
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
      let uu____10921 =
        let uu____10925 =
          let uu____10927 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10927] in
        ("Valid", uu____10925) in
      FStar_SMTEncoding_Util.mkApp uu____10921 in
    let uu____10929 =
      let uu____10930 =
        let uu____10934 =
          let uu____10935 =
            let uu____10941 =
              let uu____10942 =
                let uu____10945 =
                  let uu____10946 =
                    let uu____10952 =
                      let uu____10955 =
                        let uu____10957 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10957] in
                      [uu____10955] in
                    let uu____10960 =
                      let uu____10961 =
                        let uu____10964 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10964, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10961 in
                    (uu____10952, [xx1], uu____10960) in
                  FStar_SMTEncoding_Util.mkExists uu____10946 in
                (uu____10945, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10942 in
            ([[l_exists_a_b]], [aa; bb], uu____10941) in
          FStar_SMTEncoding_Util.mkForall uu____10935 in
        (uu____10934, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10930 in
    [uu____10929] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____11000 =
      let uu____11001 =
        let uu____11005 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____11006 = varops.mk_unique "typing_range_const" in
        (uu____11005, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____11006) in
      FStar_SMTEncoding_Util.mkAssume uu____11001 in
    [uu____11000] in
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
          let uu____11268 =
            FStar_Util.find_opt
              (fun uu____11289  ->
                 match uu____11289 with
                 | (l,uu____11299) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____11268 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____11321,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____11357 = encode_function_type_as_formula t env in
        match uu____11357 with
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
            let uu____11390 =
              (let uu____11393 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____11393) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____11390
            then
              let uu____11397 = new_term_constant_and_tok_from_lid env lid in
              match uu____11397 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____11409 =
                      let uu____11410 = FStar_Syntax_Subst.compress t_norm in
                      uu____11410.FStar_Syntax_Syntax.n in
                    match uu____11409 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11415) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____11433  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____11436 -> [] in
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
              (let uu____11445 = prims.is lid in
               if uu____11445
               then
                 let vname = varops.new_fvar lid in
                 let uu____11450 = prims.mk lid vname in
                 match uu____11450 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____11465 =
                    let uu____11471 = curried_arrow_formals_comp t_norm in
                    match uu____11471 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____11482 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____11482
                          then
                            let uu____11483 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_11486 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_11486.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_11486.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_11486.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_11486.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_11486.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_11486.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_11486.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_11486.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_11486.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_11486.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_11486.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_11486.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_11486.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_11486.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_11486.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_11486.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_11486.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_11486.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_11486.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_11486.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_11486.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_11486.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_11486.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_11486.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_11486.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_11486.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____11483
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____11493 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____11493)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____11465 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____11520 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____11520 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____11533 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_11565  ->
                                     match uu___115_11565 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____11568 =
                                           FStar_Util.prefix vars in
                                         (match uu____11568 with
                                          | (uu____11579,(xxsym,uu____11581))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____11591 =
                                                let uu____11592 =
                                                  let uu____11596 =
                                                    let uu____11597 =
                                                      let uu____11603 =
                                                        let uu____11604 =
                                                          let uu____11607 =
                                                            let uu____11608 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____11608 in
                                                          (vapp, uu____11607) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____11604 in
                                                      ([[vapp]], vars,
                                                        uu____11603) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11597 in
                                                  (uu____11596,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11592 in
                                              [uu____11591])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____11619 =
                                           FStar_Util.prefix vars in
                                         (match uu____11619 with
                                          | (uu____11630,(xxsym,uu____11632))
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
                                              let uu____11646 =
                                                let uu____11647 =
                                                  let uu____11651 =
                                                    let uu____11652 =
                                                      let uu____11658 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____11658) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11652 in
                                                  (uu____11651,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11647 in
                                              [uu____11646])
                                     | uu____11667 -> [])) in
                           let uu____11668 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____11668 with
                            | (vars,guards,env',decls1,uu____11684) ->
                                let uu____11691 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____11696 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____11696, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____11698 = encode_formula p env' in
                                      (match uu____11698 with
                                       | (g,ds) ->
                                           let uu____11705 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____11705,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____11691 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____11714 =
                                         let uu____11718 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____11718) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____11714 in
                                     let uu____11723 =
                                       let vname_decl =
                                         let uu____11728 =
                                           let uu____11734 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11740  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11734,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____11728 in
                                       let uu____11745 =
                                         let env2 =
                                           let uu___144_11749 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11749.bindings);
                                             depth = (uu___144_11749.depth);
                                             tcenv = (uu___144_11749.tcenv);
                                             warn = (uu___144_11749.warn);
                                             cache = (uu___144_11749.cache);
                                             nolabels =
                                               (uu___144_11749.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11749.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11749.current_module_name)
                                           } in
                                         let uu____11750 =
                                           let uu____11751 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11751 in
                                         if uu____11750
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____11745 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11761::uu____11762 ->
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
                                                   let uu____11785 =
                                                     let uu____11791 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11791) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11785 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11805 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____11807 =
                                             match formals with
                                             | [] ->
                                                 let uu____11816 =
                                                   let uu____11817 =
                                                     let uu____11819 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_41)
                                                       uu____11819 in
                                                   push_free_var env1 lid
                                                     vname uu____11817 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11816)
                                             | uu____11822 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____11827 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11827 in
                                                 let name_tok_corr =
                                                   let uu____11829 =
                                                     let uu____11833 =
                                                       let uu____11834 =
                                                         let uu____11840 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11840) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11834 in
                                                     (uu____11833,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11829 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____11807 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____11723 with
                                      | (decls2,env2) ->
                                          let uu____11864 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11869 =
                                              encode_term res_t1 env' in
                                            match uu____11869 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11877 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11877,
                                                  decls) in
                                          (match uu____11864 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11885 =
                                                   let uu____11889 =
                                                     let uu____11890 =
                                                       let uu____11896 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11896) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11890 in
                                                   (uu____11889,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11885 in
                                               let freshness =
                                                 let uu____11905 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11905
                                                 then
                                                   let uu____11908 =
                                                     let uu____11909 =
                                                       let uu____11915 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____11921 =
                                                         varops.next_id () in
                                                       (vname, uu____11915,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11921) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11909 in
                                                   let uu____11923 =
                                                     let uu____11925 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11925] in
                                                   uu____11908 :: uu____11923
                                                 else [] in
                                               let g =
                                                 let uu____11929 =
                                                   let uu____11931 =
                                                     let uu____11933 =
                                                       let uu____11935 =
                                                         let uu____11937 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____11937 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11935 in
                                                     FStar_List.append decls3
                                                       uu____11933 in
                                                   FStar_List.append decls2
                                                     uu____11931 in
                                                 FStar_List.append decls11
                                                   uu____11929 in
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
          let uu____11963 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11963 with
          | FStar_Pervasives_Native.None  ->
              let uu____11982 = encode_free_var env x t t_norm [] in
              (match uu____11982 with
               | (decls,env1) ->
                   let uu____11997 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____11997 with
                    | (n1,x',uu____12012) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____12024) ->
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
          let uu____12061 = encode_free_var env lid t tt quals in
          match uu____12061 with
          | (decls,env1) ->
              let uu____12072 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____12072
              then
                let uu____12076 =
                  let uu____12078 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____12078 in
                (uu____12076, env1)
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
             (fun uu____12116  ->
                fun lb  ->
                  match uu____12116 with
                  | (decls,env1) ->
                      let uu____12128 =
                        let uu____12132 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____12132
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____12128 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____12147 = FStar_Syntax_Util.head_and_args t in
    match uu____12147 with
    | (hd1,args) ->
        let uu____12173 =
          let uu____12174 = FStar_Syntax_Util.un_uinst hd1 in
          uu____12174.FStar_Syntax_Syntax.n in
        (match uu____12173 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____12178,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____12191 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____12209  ->
      fun quals  ->
        match uu____12209 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____12259 = FStar_Util.first_N nbinders formals in
              match uu____12259 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____12308  ->
                         fun uu____12309  ->
                           match (uu____12308, uu____12309) with
                           | ((formal,uu____12319),(binder,uu____12321)) ->
                               let uu____12326 =
                                 let uu____12331 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____12331) in
                               FStar_Syntax_Syntax.NT uu____12326) formals1
                      binders in
                  let extra_formals1 =
                    let uu____12336 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____12354  ->
                              match uu____12354 with
                              | (x,i) ->
                                  let uu____12361 =
                                    let uu___145_12362 = x in
                                    let uu____12363 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_12362.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_12362.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____12363
                                    } in
                                  (uu____12361, i))) in
                    FStar_All.pipe_right uu____12336
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____12375 =
                      let uu____12377 =
                        let uu____12378 = FStar_Syntax_Subst.subst subst1 t in
                        uu____12378.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                        uu____12377 in
                    let uu____12382 =
                      let uu____12383 = FStar_Syntax_Subst.compress body in
                      let uu____12384 =
                        let uu____12385 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____12385 in
                      FStar_Syntax_Syntax.extend_app_n uu____12383
                        uu____12384 in
                    uu____12382 uu____12375 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____12427 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____12427
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_12430 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_12430.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_12430.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_12430.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_12430.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_12430.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_12430.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_12430.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_12430.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_12430.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_12430.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_12430.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_12430.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_12430.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_12430.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_12430.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_12430.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_12430.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_12430.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_12430.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_12430.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_12430.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_12430.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_12430.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_12430.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_12430.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_12430.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____12451 = FStar_Syntax_Util.abs_formals e in
                match uu____12451 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____12485::uu____12486 ->
                         let uu____12494 =
                           let uu____12495 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12495.FStar_Syntax_Syntax.n in
                         (match uu____12494 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12522 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12522 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____12550 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____12550
                                   then
                                     let uu____12573 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____12573 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____12628  ->
                                                   fun uu____12629  ->
                                                     match (uu____12628,
                                                             uu____12629)
                                                     with
                                                     | ((x,uu____12639),
                                                        (b,uu____12641)) ->
                                                         let uu____12646 =
                                                           let uu____12651 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____12651) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____12646)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____12653 =
                                            let uu____12664 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____12664) in
                                          (uu____12653, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____12704 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____12704 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12756) ->
                              let uu____12761 =
                                let uu____12772 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____12772 in
                              (uu____12761, true)
                          | uu____12805 when Prims.op_Negation norm1 ->
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
                          | uu____12807 ->
                              let uu____12808 =
                                let uu____12809 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12810 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12809
                                  uu____12810 in
                              failwith uu____12808)
                     | uu____12823 ->
                         let uu____12824 =
                           let uu____12825 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12825.FStar_Syntax_Syntax.n in
                         (match uu____12824 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12852 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12852 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12870 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12870 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12918 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12948 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____12948
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12956 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____13010  ->
                            fun lb  ->
                              match uu____13010 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____13061 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____13061
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____13064 =
                                      let uu____13072 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____13072
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____13064 with
                                    | (tok,decl,env2) ->
                                        let uu____13097 =
                                          let uu____13104 =
                                            let uu____13110 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____13110, tok) in
                                          uu____13104 :: toks in
                                        (uu____13097, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12956 with
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
                        | uu____13212 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____13217 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____13217 vars)
                            else
                              (let uu____13219 =
                                 let uu____13223 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____13223) in
                               FStar_SMTEncoding_Util.mkApp uu____13219) in
                      let uu____13228 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_13231  ->
                                 match uu___116_13231 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____13232 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____13237 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____13237))) in
                      if uu____13228
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____13257;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____13259;
                                FStar_Syntax_Syntax.lbeff = uu____13260;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____13297 =
                                 let uu____13301 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____13301 with
                                 | (tcenv',uu____13312,e_t) ->
                                     let uu____13316 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____13323 -> failwith "Impossible" in
                                     (match uu____13316 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_13333 = env1 in
                                            {
                                              bindings =
                                                (uu___149_13333.bindings);
                                              depth = (uu___149_13333.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_13333.warn);
                                              cache = (uu___149_13333.cache);
                                              nolabels =
                                                (uu___149_13333.nolabels);
                                              use_zfuel_name =
                                                (uu___149_13333.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_13333.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_13333.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____13297 with
                                | (env',e1,t_norm1) ->
                                    let uu____13340 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____13340 with
                                     | ((binders,body,uu____13352,uu____13353),curry)
                                         ->
                                         ((let uu____13360 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____13360
                                           then
                                             let uu____13361 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____13362 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____13361 uu____13362
                                           else ());
                                          (let uu____13364 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____13364 with
                                           | (vars,guards,env'1,binder_decls,uu____13380)
                                               ->
                                               let body1 =
                                                 let uu____13388 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____13388
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____13391 =
                                                 let uu____13396 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____13396
                                                 then
                                                   let uu____13402 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____13403 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____13402, uu____13403)
                                                 else
                                                   (let uu____13409 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____13409)) in
                                               (match uu____13391 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____13423 =
                                                        let uu____13427 =
                                                          let uu____13428 =
                                                            let uu____13434 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____13434) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____13428 in
                                                        let uu____13440 =
                                                          let uu____13442 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____13442 in
                                                        (uu____13427,
                                                          uu____13440,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____13423 in
                                                    let uu____13444 =
                                                      let uu____13446 =
                                                        let uu____13448 =
                                                          let uu____13450 =
                                                            let uu____13452 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____13452 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____13450 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____13448 in
                                                      FStar_List.append
                                                        decls1 uu____13446 in
                                                    (uu____13444, env1))))))
                           | uu____13455 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____13474 = varops.fresh "fuel" in
                             (uu____13474, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____13477 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____13527  ->
                                     fun uu____13528  ->
                                       match (uu____13527, uu____13528) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____13606 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____13606 in
                                           let gtok =
                                             let uu____13608 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____13608 in
                                           let env3 =
                                             let uu____13610 =
                                               let uu____13612 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_43) uu____13612 in
                                             push_free_var env2 flid gtok
                                               uu____13610 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____13477 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____13698
                                 t_norm uu____13700 =
                                 match (uu____13698, uu____13700) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____13727;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____13728;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____13745 =
                                       let uu____13749 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____13749 with
                                       | (tcenv',uu____13764,e_t) ->
                                           let uu____13768 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13775 ->
                                                 failwith "Impossible" in
                                           (match uu____13768 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13785 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13785.bindings);
                                                    depth =
                                                      (uu___150_13785.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13785.warn);
                                                    cache =
                                                      (uu___150_13785.cache);
                                                    nolabels =
                                                      (uu___150_13785.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13785.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13785.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13785.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____13745 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13795 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____13795
                                            then
                                              let uu____13796 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13797 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13798 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13796 uu____13797
                                                uu____13798
                                            else ());
                                           (let uu____13800 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13800 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13822 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____13822
                                                  then
                                                    let uu____13823 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13824 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13825 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13826 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13823 uu____13824
                                                      uu____13825 uu____13826
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13830 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____13830 with
                                                  | (vars,guards,env'1,binder_decls,uu____13848)
                                                      ->
                                                      let decl_g =
                                                        let uu____13856 =
                                                          let uu____13862 =
                                                            let uu____13864 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13864 in
                                                          (g, uu____13862,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13856 in
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
                                                        let uu____13879 =
                                                          let uu____13883 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13883) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13879 in
                                                      let gsapp =
                                                        let uu____13889 =
                                                          let uu____13893 =
                                                            let uu____13895 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13895 ::
                                                              vars_tm in
                                                          (g, uu____13893) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13889 in
                                                      let gmax =
                                                        let uu____13899 =
                                                          let uu____13903 =
                                                            let uu____13905 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13905 ::
                                                              vars_tm in
                                                          (g, uu____13903) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13899 in
                                                      let body1 =
                                                        let uu____13909 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13909
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____13911 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13911 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13922
                                                               =
                                                               let uu____13926
                                                                 =
                                                                 let uu____13927
                                                                   =
                                                                   let uu____13935
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
                                                                    uu____13935) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13927 in
                                                               let uu____13946
                                                                 =
                                                                 let uu____13948
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____13948 in
                                                               (uu____13926,
                                                                 uu____13946,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13922 in
                                                           let eqn_f =
                                                             let uu____13951
                                                               =
                                                               let uu____13955
                                                                 =
                                                                 let uu____13956
                                                                   =
                                                                   let uu____13962
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13962) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13956 in
                                                               (uu____13955,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13951 in
                                                           let eqn_g' =
                                                             let uu____13970
                                                               =
                                                               let uu____13974
                                                                 =
                                                                 let uu____13975
                                                                   =
                                                                   let uu____13981
                                                                    =
                                                                    let uu____13982
                                                                    =
                                                                    let uu____13985
                                                                    =
                                                                    let uu____13986
                                                                    =
                                                                    let uu____13990
                                                                    =
                                                                    let uu____13992
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____13992
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13990) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13986 in
                                                                    (gsapp,
                                                                    uu____13985) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13982 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13981) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13975 in
                                                               (uu____13974,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13970 in
                                                           let uu____14004 =
                                                             let uu____14009
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____14009
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____14026)
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
                                                                    let uu____14041
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____14041
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____14044
                                                                    =
                                                                    let uu____14048
                                                                    =
                                                                    let uu____14049
                                                                    =
                                                                    let uu____14055
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____14055) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14049 in
                                                                    (uu____14048,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14044 in
                                                                 let uu____14066
                                                                   =
                                                                   let uu____14070
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____14070
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____14078
                                                                    =
                                                                    let uu____14080
                                                                    =
                                                                    let uu____14081
                                                                    =
                                                                    let uu____14085
                                                                    =
                                                                    let uu____14086
                                                                    =
                                                                    let uu____14092
                                                                    =
                                                                    let uu____14093
                                                                    =
                                                                    let uu____14096
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____14096,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14093 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____14092) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14086 in
                                                                    (uu____14085,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14081 in
                                                                    [uu____14080] in
                                                                    (d3,
                                                                    uu____14078) in
                                                                 (match uu____14066
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____14004
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
                               let uu____14131 =
                                 let uu____14138 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____14186  ->
                                      fun uu____14187  ->
                                        match (uu____14186, uu____14187) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____14273 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____14273 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____14138 in
                               (match uu____14131 with
                                | (decls2,eqns,env01) ->
                                    let uu____14313 =
                                      let isDeclFun uu___117_14321 =
                                        match uu___117_14321 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____14322 -> true
                                        | uu____14328 -> false in
                                      let uu____14329 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____14329
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____14313 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____14359 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____14359
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
        let uu____14393 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____14393 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____14396 = encode_sigelt' env se in
      match uu____14396 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____14406 =
                  let uu____14407 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____14407 in
                [uu____14406]
            | uu____14408 ->
                let uu____14409 =
                  let uu____14411 =
                    let uu____14412 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____14412 in
                  uu____14411 :: g in
                let uu____14413 =
                  let uu____14415 =
                    let uu____14416 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____14416 in
                  [uu____14415] in
                FStar_List.append uu____14409 uu____14413 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____14426 =
          let uu____14427 = FStar_Syntax_Subst.compress t in
          uu____14427.FStar_Syntax_Syntax.n in
        match uu____14426 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____14431)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____14434 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14437 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____14440 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____14442 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14444 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____14452 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____14455 =
            let uu____14456 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____14456 Prims.op_Negation in
          if uu____14455
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____14476 ->
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
               let uu____14496 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____14496 with
               | (aname,atok,env2) ->
                   let uu____14506 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____14506 with
                    | (formals,uu____14516) ->
                        let uu____14523 =
                          let uu____14526 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____14526 env2 in
                        (match uu____14523 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____14534 =
                                 let uu____14535 =
                                   let uu____14541 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____14550  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____14541,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____14535 in
                               [uu____14534;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____14557 =
                               let aux uu____14586 uu____14587 =
                                 match (uu____14586, uu____14587) with
                                 | ((bv,uu____14614),(env3,acc_sorts,acc)) ->
                                     let uu____14635 = gen_term_var env3 bv in
                                     (match uu____14635 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____14557 with
                              | (uu____14673,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____14687 =
                                      let uu____14691 =
                                        let uu____14692 =
                                          let uu____14698 =
                                            let uu____14699 =
                                              let uu____14702 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____14702) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____14699 in
                                          ([[app]], xs_sorts, uu____14698) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14692 in
                                      (uu____14691,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14687 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____14714 =
                                      let uu____14718 =
                                        let uu____14719 =
                                          let uu____14725 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____14725) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14719 in
                                      (uu____14718,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14714 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____14735 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____14735 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14751,uu____14752)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____14753 = new_term_constant_and_tok_from_lid env lid in
          (match uu____14753 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14764,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____14769 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_14772  ->
                      match uu___118_14772 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____14773 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____14776 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14777 -> false)) in
            Prims.op_Negation uu____14769 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____14783 = encode_top_level_val env fv t quals in
             match uu____14783 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____14795 =
                   let uu____14797 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14797 in
                 (uu____14795, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____14803 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____14803 with
           | (uu____14808,f1) ->
               let uu____14810 = encode_formula f1 env in
               (match uu____14810 with
                | (f2,decls) ->
                    let g =
                      let uu____14819 =
                        let uu____14820 =
                          let uu____14824 =
                            let uu____14826 =
                              let uu____14827 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____14827 in
                            FStar_Pervasives_Native.Some uu____14826 in
                          let uu____14828 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____14824, uu____14828) in
                        FStar_SMTEncoding_Util.mkAssume uu____14820 in
                      [uu____14819] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14832) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____14839 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14854 =
                       let uu____14856 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14856.FStar_Syntax_Syntax.fv_name in
                     uu____14854.FStar_Syntax_Syntax.v in
                   let uu____14857 =
                     let uu____14858 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14858 in
                   if uu____14857
                   then
                     let val_decl =
                       let uu___151_14873 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14873.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14873.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_14873.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____14877 = encode_sigelt' env1 val_decl in
                     match uu____14877 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____14839 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14894,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14896;
                          FStar_Syntax_Syntax.lbtyp = uu____14897;
                          FStar_Syntax_Syntax.lbeff = uu____14898;
                          FStar_Syntax_Syntax.lbdef = uu____14899;_}::[]),uu____14900)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____14912 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14912 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____14931 =
                   let uu____14933 =
                     let uu____14934 =
                       let uu____14938 =
                         let uu____14939 =
                           let uu____14945 =
                             let uu____14946 =
                               let uu____14949 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14949) in
                             FStar_SMTEncoding_Util.mkEq uu____14946 in
                           ([[b2t_x]], [xx], uu____14945) in
                         FStar_SMTEncoding_Util.mkForall uu____14939 in
                       (uu____14938,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14934 in
                   [uu____14933] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____14931 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14966,uu____14967) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_14973  ->
                  match uu___119_14973 with
                  | FStar_Syntax_Syntax.Discriminator uu____14974 -> true
                  | uu____14975 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14977,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14985 =
                     let uu____14986 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14986.FStar_Ident.idText in
                   uu____14985 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_14989  ->
                     match uu___120_14989 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14990 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14993) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_15003  ->
                  match uu___121_15003 with
                  | FStar_Syntax_Syntax.Projector uu____15004 -> true
                  | uu____15007 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____15010 = try_lookup_free_var env l in
          (match uu____15010 with
           | FStar_Pervasives_Native.Some uu____15014 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_15017 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_15017.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_15017.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_15017.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____15023) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15033) ->
          let uu____15038 = encode_sigelts env ses in
          (match uu____15038 with
           | (g,env1) ->
               let uu____15048 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_15062  ->
                         match uu___122_15062 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____15063;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____15064;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____15065;_}
                             -> false
                         | uu____15067 -> true)) in
               (match uu____15048 with
                | (g',inversions) ->
                    let uu____15076 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_15088  ->
                              match uu___123_15088 with
                              | FStar_SMTEncoding_Term.DeclFun uu____15089 ->
                                  true
                              | uu____15095 -> false)) in
                    (match uu____15076 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____15106,tps,k,uu____15109,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_15120  ->
                    match uu___124_15120 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____15121 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____15128 = c in
              match uu____15128 with
              | (name,args,uu____15132,uu____15133,uu____15134) ->
                  let uu____15137 =
                    let uu____15138 =
                      let uu____15144 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____15155  ->
                                match uu____15155 with
                                | (uu____15159,sort,uu____15161) -> sort)) in
                      (name, uu____15144, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____15138 in
                  [uu____15137]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____15179 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____15184 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____15184 FStar_Option.isNone)) in
            if uu____15179
            then []
            else
              (let uu____15201 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____15201 with
               | (xxsym,xx) ->
                   let uu____15207 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____15236  ->
                             fun l  ->
                               match uu____15236 with
                               | (out,decls) ->
                                   let uu____15248 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____15248 with
                                    | (uu____15254,data_t) ->
                                        let uu____15256 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____15256 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____15285 =
                                                 let uu____15286 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____15286.FStar_Syntax_Syntax.n in
                                               match uu____15285 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____15294,indices) ->
                                                   indices
                                               | uu____15310 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____15327  ->
                                                         match uu____15327
                                                         with
                                                         | (x,uu____15331) ->
                                                             let uu____15332
                                                               =
                                                               let uu____15333
                                                                 =
                                                                 let uu____15337
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____15337,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____15333 in
                                                             push_term_var
                                                               env1 x
                                                               uu____15332)
                                                    env) in
                                             let uu____15339 =
                                               encode_args indices env1 in
                                             (match uu____15339 with
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
                                                      let uu____15363 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____15374
                                                                 =
                                                                 let uu____15377
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____15377,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____15374)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____15363
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____15379 =
                                                      let uu____15380 =
                                                        let uu____15383 =
                                                          let uu____15384 =
                                                            let uu____15387 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____15387,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____15384 in
                                                        (out, uu____15383) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____15380 in
                                                    (uu____15379,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____15207 with
                    | (data_ax,decls) ->
                        let uu____15395 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____15395 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____15409 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____15409 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____15412 =
                                 let uu____15416 =
                                   let uu____15417 =
                                     let uu____15423 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____15431 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____15423,
                                       uu____15431) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____15417 in
                                 let uu____15439 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____15416,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____15439) in
                               FStar_SMTEncoding_Util.mkAssume uu____15412 in
                             let pattern_guarded_inversion =
                               let uu____15443 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____15443
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____15454 =
                                   let uu____15455 =
                                     let uu____15459 =
                                       let uu____15460 =
                                         let uu____15466 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____15474 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____15466, uu____15474) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____15460 in
                                     let uu____15482 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____15459,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____15482) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____15455 in
                                 [uu____15454]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____15485 =
            let uu____15493 =
              let uu____15494 = FStar_Syntax_Subst.compress k in
              uu____15494.FStar_Syntax_Syntax.n in
            match uu____15493 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____15523 -> (tps, k) in
          (match uu____15485 with
           | (formals,res) ->
               let uu____15538 = FStar_Syntax_Subst.open_term formals res in
               (match uu____15538 with
                | (formals1,res1) ->
                    let uu____15545 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____15545 with
                     | (vars,guards,env',binder_decls,uu____15560) ->
                         let uu____15567 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____15567 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____15580 =
                                  let uu____15584 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____15584) in
                                FStar_SMTEncoding_Util.mkApp uu____15580 in
                              let uu____15589 =
                                let tname_decl =
                                  let uu____15595 =
                                    let uu____15596 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____15614  ->
                                              match uu____15614 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____15622 = varops.next_id () in
                                    (tname, uu____15596,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____15622, false) in
                                  constructor_or_logic_type_decl uu____15595 in
                                let uu____15627 =
                                  match vars with
                                  | [] ->
                                      let uu____15634 =
                                        let uu____15635 =
                                          let uu____15637 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____15637 in
                                        push_free_var env1 t tname
                                          uu____15635 in
                                      ([], uu____15634)
                                  | uu____15641 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____15647 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____15647 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____15656 =
                                          let uu____15660 =
                                            let uu____15661 =
                                              let uu____15669 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____15669) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____15661 in
                                          (uu____15660,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____15656 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____15627 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____15589 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____15692 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____15692 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____15709 =
                                               let uu____15710 =
                                                 let uu____15714 =
                                                   let uu____15715 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____15715 in
                                                 (uu____15714,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15710 in
                                             [uu____15709]
                                           else [] in
                                         let uu____15718 =
                                           let uu____15720 =
                                             let uu____15722 =
                                               let uu____15723 =
                                                 let uu____15727 =
                                                   let uu____15728 =
                                                     let uu____15734 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____15734) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____15728 in
                                                 (uu____15727,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15723 in
                                             [uu____15722] in
                                           FStar_List.append karr uu____15720 in
                                         FStar_List.append decls1 uu____15718 in
                                   let aux =
                                     let uu____15743 =
                                       let uu____15745 =
                                         inversion_axioms tapp vars in
                                       let uu____15747 =
                                         let uu____15749 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____15749] in
                                       FStar_List.append uu____15745
                                         uu____15747 in
                                     FStar_List.append kindingAx uu____15743 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15754,uu____15755,uu____15756,uu____15757,uu____15758)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15763,t,uu____15765,n_tps,uu____15767) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____15772 = new_term_constant_and_tok_from_lid env d in
          (match uu____15772 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____15783 = FStar_Syntax_Util.arrow_formals t in
               (match uu____15783 with
                | (formals,t_res) ->
                    let uu____15805 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____15805 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____15814 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____15814 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____15856 =
                                            mk_term_projector_name d x in
                                          (uu____15856,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15858 =
                                  let uu____15868 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15868, true) in
                                FStar_All.pipe_right uu____15858
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
                              let uu____15890 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____15890 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15898::uu____15899 ->
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
                                         let uu____15924 =
                                           let uu____15930 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15930) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15924
                                     | uu____15943 -> tok_typing in
                                   let uu____15948 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____15948 with
                                    | (vars',guards',env'',decls_formals,uu____15963)
                                        ->
                                        let uu____15970 =
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
                                        (match uu____15970 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15989 ->
                                                   let uu____15993 =
                                                     let uu____15994 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15994 in
                                                   [uu____15993] in
                                             let encode_elim uu____16001 =
                                               let uu____16002 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____16002 with
                                               | (head1,args) ->
                                                   let uu____16031 =
                                                     let uu____16032 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____16032.FStar_Syntax_Syntax.n in
                                                   (match uu____16031 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____16039;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____16040;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____16041;_},uu____16042)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____16048 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____16048
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
                                                                 | uu____16077
                                                                    ->
                                                                    let uu____16078
                                                                    =
                                                                    let uu____16079
                                                                    =
                                                                    let uu____16082
                                                                    =
                                                                    let uu____16083
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16083 in
                                                                    (uu____16082,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____16079 in
                                                                    raise
                                                                    uu____16078 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16094
                                                                    =
                                                                    let uu____16095
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16095 in
                                                                    if
                                                                    uu____16094
                                                                    then
                                                                    let uu____16102
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____16102]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____16104
                                                               =
                                                               let uu____16111
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____16144
                                                                     ->
                                                                    fun
                                                                    uu____16145
                                                                     ->
                                                                    match 
                                                                    (uu____16144,
                                                                    uu____16145)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16196
                                                                    =
                                                                    let uu____16200
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____16200 in
                                                                    (match uu____16196
                                                                    with
                                                                    | 
                                                                    (uu____16207,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16213
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____16213
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16215
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____16215
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
                                                                 uu____16111 in
                                                             (match uu____16104
                                                              with
                                                              | (uu____16223,arg_vars,elim_eqns_or_guards,uu____16226)
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
                                                                    let uu____16245
                                                                    =
                                                                    let uu____16249
                                                                    =
                                                                    let uu____16250
                                                                    =
                                                                    let uu____16256
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16262
                                                                    =
                                                                    let uu____16263
                                                                    =
                                                                    let uu____16266
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____16266) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16263 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16256,
                                                                    uu____16262) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16250 in
                                                                    (uu____16249,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16245 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____16279
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____16279,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____16281
                                                                    =
                                                                    let uu____16285
                                                                    =
                                                                    let uu____16286
                                                                    =
                                                                    let uu____16292
                                                                    =
                                                                    let uu____16295
                                                                    =
                                                                    let uu____16297
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____16297] in
                                                                    [uu____16295] in
                                                                    let uu____16300
                                                                    =
                                                                    let uu____16301
                                                                    =
                                                                    let uu____16304
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____16305
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____16304,
                                                                    uu____16305) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16301 in
                                                                    (uu____16292,
                                                                    [x],
                                                                    uu____16300) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16286 in
                                                                    let uu____16315
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____16285,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16315) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16281
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16320
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
                                                                    (let uu____16337
                                                                    =
                                                                    let uu____16338
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____16338
                                                                    dapp1 in
                                                                    [uu____16337]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____16320
                                                                    FStar_List.flatten in
                                                                    let uu____16342
                                                                    =
                                                                    let uu____16346
                                                                    =
                                                                    let uu____16347
                                                                    =
                                                                    let uu____16353
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16359
                                                                    =
                                                                    let uu____16360
                                                                    =
                                                                    let uu____16363
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16363) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16360 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16353,
                                                                    uu____16359) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16347 in
                                                                    (uu____16346,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16342) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____16375 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____16375
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
                                                                 | uu____16404
                                                                    ->
                                                                    let uu____16405
                                                                    =
                                                                    let uu____16406
                                                                    =
                                                                    let uu____16409
                                                                    =
                                                                    let uu____16410
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16410 in
                                                                    (uu____16409,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____16406 in
                                                                    raise
                                                                    uu____16405 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16421
                                                                    =
                                                                    let uu____16422
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16422 in
                                                                    if
                                                                    uu____16421
                                                                    then
                                                                    let uu____16429
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____16429]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____16431
                                                               =
                                                               let uu____16438
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____16471
                                                                     ->
                                                                    fun
                                                                    uu____16472
                                                                     ->
                                                                    match 
                                                                    (uu____16471,
                                                                    uu____16472)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16523
                                                                    =
                                                                    let uu____16527
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____16527 in
                                                                    (match uu____16523
                                                                    with
                                                                    | 
                                                                    (uu____16534,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16540
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____16540
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16542
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____16542
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
                                                                 uu____16438 in
                                                             (match uu____16431
                                                              with
                                                              | (uu____16550,arg_vars,elim_eqns_or_guards,uu____16553)
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
                                                                    let uu____16572
                                                                    =
                                                                    let uu____16576
                                                                    =
                                                                    let uu____16577
                                                                    =
                                                                    let uu____16583
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16589
                                                                    =
                                                                    let uu____16590
                                                                    =
                                                                    let uu____16593
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____16593) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16590 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16583,
                                                                    uu____16589) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16577 in
                                                                    (uu____16576,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16572 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____16606
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____16606,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____16608
                                                                    =
                                                                    let uu____16612
                                                                    =
                                                                    let uu____16613
                                                                    =
                                                                    let uu____16619
                                                                    =
                                                                    let uu____16622
                                                                    =
                                                                    let uu____16624
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____16624] in
                                                                    [uu____16622] in
                                                                    let uu____16627
                                                                    =
                                                                    let uu____16628
                                                                    =
                                                                    let uu____16631
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____16632
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____16631,
                                                                    uu____16632) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16628 in
                                                                    (uu____16619,
                                                                    [x],
                                                                    uu____16627) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16613 in
                                                                    let uu____16642
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____16612,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16642) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16608
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16647
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
                                                                    (let uu____16664
                                                                    =
                                                                    let uu____16665
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____16665
                                                                    dapp1 in
                                                                    [uu____16664]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____16647
                                                                    FStar_List.flatten in
                                                                    let uu____16669
                                                                    =
                                                                    let uu____16673
                                                                    =
                                                                    let uu____16674
                                                                    =
                                                                    let uu____16680
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16686
                                                                    =
                                                                    let uu____16687
                                                                    =
                                                                    let uu____16690
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16690) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16687 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16680,
                                                                    uu____16686) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16674 in
                                                                    (uu____16673,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16669) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____16700 ->
                                                        ((let uu____16702 =
                                                            let uu____16703 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____16704 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____16703
                                                              uu____16704 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____16702);
                                                         ([], []))) in
                                             let uu____16707 = encode_elim () in
                                             (match uu____16707 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____16719 =
                                                      let uu____16721 =
                                                        let uu____16723 =
                                                          let uu____16725 =
                                                            let uu____16727 =
                                                              let uu____16728
                                                                =
                                                                let uu____16734
                                                                  =
                                                                  let uu____16736
                                                                    =
                                                                    let uu____16737
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16737 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____16736 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____16734) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____16728 in
                                                            [uu____16727] in
                                                          let uu____16740 =
                                                            let uu____16742 =
                                                              let uu____16744
                                                                =
                                                                let uu____16746
                                                                  =
                                                                  let uu____16748
                                                                    =
                                                                    let uu____16750
                                                                    =
                                                                    let uu____16752
                                                                    =
                                                                    let uu____16753
                                                                    =
                                                                    let uu____16757
                                                                    =
                                                                    let uu____16758
                                                                    =
                                                                    let uu____16764
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16764) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16758 in
                                                                    (uu____16757,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16753 in
                                                                    let uu____16771
                                                                    =
                                                                    let uu____16773
                                                                    =
                                                                    let uu____16774
                                                                    =
                                                                    let uu____16778
                                                                    =
                                                                    let uu____16779
                                                                    =
                                                                    let uu____16785
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____16791
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16785,
                                                                    uu____16791) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16779 in
                                                                    (uu____16778,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16774 in
                                                                    [uu____16773] in
                                                                    uu____16752
                                                                    ::
                                                                    uu____16771 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____16750 in
                                                                  FStar_List.append
                                                                    uu____16748
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____16746 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____16744 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____16742 in
                                                          FStar_List.append
                                                            uu____16725
                                                            uu____16740 in
                                                        FStar_List.append
                                                          decls3 uu____16723 in
                                                      FStar_List.append
                                                        decls2 uu____16721 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____16719 in
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
           (fun uu____16819  ->
              fun se  ->
                match uu____16819 with
                | (g,env1) ->
                    let uu____16831 = encode_sigelt env1 se in
                    (match uu____16831 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16869 =
        match uu____16869 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____16887 ->
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
                 ((let uu____16892 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____16892
                   then
                     let uu____16893 = FStar_Syntax_Print.bv_to_string x in
                     let uu____16894 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____16895 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16893 uu____16894 uu____16895
                   else ());
                  (let uu____16897 = encode_term t1 env1 in
                   match uu____16897 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____16907 =
                         let uu____16911 =
                           let uu____16912 =
                             let uu____16913 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____16913
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____16912 in
                         new_term_constant_from_string env1 x uu____16911 in
                       (match uu____16907 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____16924 = FStar_Options.log_queries () in
                              if uu____16924
                              then
                                let uu____16926 =
                                  let uu____16927 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____16928 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____16929 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16927 uu____16928 uu____16929 in
                                FStar_Pervasives_Native.Some uu____16926
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____16940,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____16949 = encode_free_var env1 fv t t_norm [] in
                 (match uu____16949 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____16962,se,uu____16964) ->
                 let uu____16967 = encode_sigelt env1 se in
                 (match uu____16967 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16977,se) ->
                 let uu____16981 = encode_sigelt env1 se in
                 (match uu____16981 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16991 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16991 with | (uu____17003,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____17055  ->
            match uu____17055 with
            | (l,uu____17062,uu____17063) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____17090  ->
            match uu____17090 with
            | (l,uu____17098,uu____17099) ->
                let uu____17104 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                    (FStar_Pervasives_Native.fst l) in
                let uu____17105 =
                  let uu____17107 =
                    let uu____17108 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____17108 in
                  [uu____17107] in
                uu____17104 :: uu____17105)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____17120 =
      let uu____17122 =
        let uu____17123 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____17125 =
          let uu____17126 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____17126 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____17123;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____17125
        } in
      [uu____17122] in
    FStar_ST.write last_env uu____17120
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____17138 = FStar_ST.read last_env in
      match uu____17138 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17144 ->
          let uu___153_17146 = e in
          let uu____17147 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_17146.bindings);
            depth = (uu___153_17146.depth);
            tcenv;
            warn = (uu___153_17146.warn);
            cache = (uu___153_17146.cache);
            nolabels = (uu___153_17146.nolabels);
            use_zfuel_name = (uu___153_17146.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_17146.encode_non_total_function_typ);
            current_module_name = uu____17147
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____17152 = FStar_ST.read last_env in
    match uu____17152 with
    | [] -> failwith "Empty env stack"
    | uu____17157::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____17166  ->
    let uu____17167 = FStar_ST.read last_env in
    match uu____17167 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_17178 = hd1 in
          {
            bindings = (uu___154_17178.bindings);
            depth = (uu___154_17178.depth);
            tcenv = (uu___154_17178.tcenv);
            warn = (uu___154_17178.warn);
            cache = refs;
            nolabels = (uu___154_17178.nolabels);
            use_zfuel_name = (uu___154_17178.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_17178.encode_non_total_function_typ);
            current_module_name = (uu___154_17178.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____17185  ->
    let uu____17186 = FStar_ST.read last_env in
    match uu____17186 with
    | [] -> failwith "Popping an empty stack"
    | uu____17191::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____17200  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____17204  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____17208  ->
    let uu____17209 = FStar_ST.read last_env in
    match uu____17209 with
    | hd1::uu____17215::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____17221 -> failwith "Impossible"
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
        | (uu____17280::uu____17281,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_17287 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_17287.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_17287.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_17287.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17288 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____17301 =
        let uu____17303 =
          let uu____17304 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____17304 in
        let uu____17305 = open_fact_db_tags env in uu____17303 :: uu____17305 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17301
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
      let uu____17322 = encode_sigelt env se in
      match uu____17322 with
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
        let uu____17349 = FStar_Options.log_queries () in
        if uu____17349
        then
          let uu____17351 =
            let uu____17352 =
              let uu____17353 =
                let uu____17354 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____17354 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____17353 in
            FStar_SMTEncoding_Term.Caption uu____17352 in
          uu____17351 :: decls
        else decls in
      let env =
        let uu____17361 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17361 tcenv in
      let uu____17362 = encode_top_level_facts env se in
      match uu____17362 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____17371 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____17371))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____17384 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____17384
       then
         let uu____17385 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____17385
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____17415  ->
                 fun se  ->
                   match uu____17415 with
                   | (g,env2) ->
                       let uu____17427 = encode_top_level_facts env2 se in
                       (match uu____17427 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____17440 =
         encode_signature
           (let uu___156_17446 = env in
            {
              bindings = (uu___156_17446.bindings);
              depth = (uu___156_17446.depth);
              tcenv = (uu___156_17446.tcenv);
              warn = false;
              cache = (uu___156_17446.cache);
              nolabels = (uu___156_17446.nolabels);
              use_zfuel_name = (uu___156_17446.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_17446.encode_non_total_function_typ);
              current_module_name = (uu___156_17446.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____17440 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____17458 = FStar_Options.log_queries () in
             if uu____17458
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_17465 = env1 in
               {
                 bindings = (uu___157_17465.bindings);
                 depth = (uu___157_17465.depth);
                 tcenv = (uu___157_17465.tcenv);
                 warn = true;
                 cache = (uu___157_17465.cache);
                 nolabels = (uu___157_17465.nolabels);
                 use_zfuel_name = (uu___157_17465.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_17465.encode_non_total_function_typ);
                 current_module_name = (uu___157_17465.current_module_name)
               });
            (let uu____17467 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____17467
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
        (let uu____17505 =
           let uu____17506 = FStar_TypeChecker_Env.current_module tcenv in
           uu____17506.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17505);
        (let env =
           let uu____17508 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____17508 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____17517 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____17538 = aux rest in
                 (match uu____17538 with
                  | (out,rest1) ->
                      let t =
                        let uu____17556 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____17556 with
                        | FStar_Pervasives_Native.Some uu____17560 ->
                            let uu____17561 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____17561
                              x.FStar_Syntax_Syntax.sort
                        | uu____17562 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____17565 =
                        let uu____17567 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_17570 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_17570.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_17570.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____17567 :: out in
                      (uu____17565, rest1))
             | uu____17573 -> ([], bindings1) in
           let uu____17577 = aux bindings in
           match uu____17577 with
           | (closing,bindings1) ->
               let uu____17591 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____17591, bindings1) in
         match uu____17517 with
         | (q1,bindings1) ->
             let uu____17604 =
               let uu____17607 =
                 FStar_List.filter
                   (fun uu___125_17611  ->
                      match uu___125_17611 with
                      | FStar_TypeChecker_Env.Binding_sig uu____17612 ->
                          false
                      | uu____17616 -> true) bindings1 in
               encode_env_bindings env uu____17607 in
             (match uu____17604 with
              | (env_decls,env1) ->
                  ((let uu____17627 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____17627
                    then
                      let uu____17628 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17628
                    else ());
                   (let uu____17630 = encode_formula q1 env1 in
                    match uu____17630 with
                    | (phi,qdecls) ->
                        let uu____17642 =
                          let uu____17645 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17645 phi in
                        (match uu____17642 with
                         | (labels,phi1) ->
                             let uu____17655 = encode_labels labels in
                             (match uu____17655 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____17676 =
                                      let uu____17680 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____17681 =
                                        varops.mk_unique "@query" in
                                      (uu____17680,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17681) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17676 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____17696 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17696 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____17698 = encode_formula q env in
       match uu____17698 with
       | (f,uu____17702) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____17704) -> true
             | uu____17707 -> false)))