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
      ((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
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
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_udiv_lid))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mod_lid))
           ||
           (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_ult_lid))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_uext_lid))
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
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3757::(sz_arg,uu____3759)::uu____3760::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____3794 = FStar_List.tail args_e in
                  let uu____3796 =
                    let uu____3798 = getInteger sz_arg.FStar_Syntax_Syntax.n in
                    FStar_Pervasives_Native.Some uu____3798 in
                  (uu____3794, uu____3796)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____3802::(sz_arg,uu____3804)::uu____3805::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____3839 = FStar_Syntax_Print.term_to_string sz_arg in
                  failwith uu____3839
              | uu____3844 -> (args_e, FStar_Pervasives_Native.None) in
            (match uu____3746 with
             | (arg_tms,ext_sz) ->
                 let uu____3859 = encode_args arg_tms env in
                 (match uu____3859 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____3872 -> failwith "Impossible" in
                      let unary arg_tms2 =
                        let uu____3879 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____3879 in
                      let unary_arith arg_tms2 =
                        let uu____3886 = FStar_List.hd arg_tms2 in
                        FStar_SMTEncoding_Term.unboxInt uu____3886 in
                      let binary arg_tms2 =
                        let uu____3895 =
                          let uu____3896 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3896 in
                        let uu____3897 =
                          let uu____3898 =
                            let uu____3899 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____3899 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3898 in
                        (uu____3895, uu____3897) in
                      let binary_arith arg_tms2 =
                        let uu____3909 =
                          let uu____3910 = FStar_List.hd arg_tms2 in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____3910 in
                        let uu____3911 =
                          let uu____3912 =
                            let uu____3913 = FStar_List.tl arg_tms2 in
                            FStar_List.hd uu____3913 in
                          FStar_SMTEncoding_Term.unboxInt uu____3912 in
                        (uu____3909, uu____3911) in
                      let mk_bv op mk_args resBox ts =
                        let uu____3957 =
                          let uu____3958 = mk_args ts in op uu____3958 in
                        FStar_All.pipe_right uu____3957 resBox in
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
                        let uu____4019 =
                          let uu____4022 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "Not a constant bitvector size" in
                          FStar_SMTEncoding_Util.mkBvUext uu____4022 in
                        let uu____4024 =
                          let uu____4027 =
                            let uu____4028 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "Not a constant bitvector size" in
                            sz + uu____4028 in
                          FStar_SMTEncoding_Term.boxBitVec uu____4027 in
                        mk_bv uu____4019 unary uu____4024 arg_tms2 in
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
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)] in
                      let uu____4134 =
                        let uu____4140 =
                          FStar_List.tryFind
                            (fun uu____4155  ->
                               match uu____4155 with
                               | (l,uu____4162) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops in
                        FStar_All.pipe_right uu____4140 FStar_Util.must in
                      (match uu____4134 with
                       | (uu____4188,op) ->
                           let uu____4196 = op arg_tms1 in
                           (uu____4196, (FStar_List.append sz_decls decls)))))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____4204 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____4204
       then
         let uu____4205 = FStar_Syntax_Print.tag_of_term t in
         let uu____4206 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____4207 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____4205 uu____4206
           uu____4207
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____4211 ->
           let uu____4226 =
             let uu____4227 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4228 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4229 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4230 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4227
               uu____4228 uu____4229 uu____4230 in
           failwith uu____4226
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____4233 =
             let uu____4234 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____4235 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____4236 = FStar_Syntax_Print.term_to_string t0 in
             let uu____4237 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____4234
               uu____4235 uu____4236 uu____4237 in
           failwith uu____4233
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____4241 =
             let uu____4242 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____4242 in
           failwith uu____4241
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____4247) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____4277) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____4286 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____4286, [])
       | FStar_Syntax_Syntax.Tm_type uu____4288 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____4291) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____4297 = encode_const c in (uu____4297, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____4312 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____4312 with
            | (binders1,res) ->
                let uu____4319 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____4319
                then
                  let uu____4322 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____4322 with
                   | (vars,guards,env',decls,uu____4337) ->
                       let fsym =
                         let uu____4347 = varops.fresh "f" in
                         (uu____4347, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____4350 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_4356 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_4356.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_4356.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_4356.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_4356.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_4356.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_4356.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_4356.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_4356.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_4356.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_4356.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_4356.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_4356.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_4356.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_4356.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_4356.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_4356.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_4356.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_4356.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_4356.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_4356.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_4356.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_4356.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_4356.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_4356.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_4356.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_4356.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____4350 with
                        | (pre_opt,res_t) ->
                            let uu____4363 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____4363 with
                             | (res_pred,decls') ->
                                 let uu____4370 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____4377 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____4377, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____4380 =
                                         encode_formula pre env' in
                                       (match uu____4380 with
                                        | (guard,decls0) ->
                                            let uu____4388 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____4388, decls0)) in
                                 (match uu____4370 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____4396 =
                                          let uu____4402 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____4402) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4396 in
                                      let cvars =
                                        let uu____4412 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____4412
                                          (FStar_List.filter
                                             (fun uu____4421  ->
                                                match uu____4421 with
                                                | (x,uu____4425) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4436 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4436 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____4441 =
                                             let uu____4442 =
                                               let uu____4446 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____4446) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4442 in
                                           (uu____4441,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____4457 =
                                               let uu____4458 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____4458 in
                                             varops.mk_unique uu____4457 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____4465 =
                                               FStar_Options.log_queries () in
                                             if uu____4465
                                             then
                                               let uu____4467 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4467
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____4473 =
                                               let uu____4477 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____4477) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4473 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____4485 =
                                               let uu____4489 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____4489,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4485 in
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
                                             let uu____4502 =
                                               let uu____4506 =
                                                 let uu____4507 =
                                                   let uu____4513 =
                                                     let uu____4514 =
                                                       let uu____4517 =
                                                         let uu____4518 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____4518 in
                                                       (f_has_t, uu____4517) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____4514 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____4513) in
                                                 mkForall_fuel uu____4507 in
                                               (uu____4506,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4502 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____4531 =
                                               let uu____4535 =
                                                 let uu____4536 =
                                                   let uu____4542 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____4542) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____4536 in
                                               (uu____4535,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____4531 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____4556 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____4556);
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
                     let uu____4567 =
                       let uu____4571 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____4571,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4567 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____4580 =
                       let uu____4584 =
                         let uu____4585 =
                           let uu____4591 =
                             let uu____4592 =
                               let uu____4595 =
                                 let uu____4596 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____4596 in
                               (f_has_t, uu____4595) in
                             FStar_SMTEncoding_Util.mkImp uu____4592 in
                           ([[f_has_t]], [fsym], uu____4591) in
                         mkForall_fuel uu____4585 in
                       (uu____4584, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____4580 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____4610 ->
           let uu____4615 =
             let uu____4618 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____4618 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____4623;
                 FStar_Syntax_Syntax.pos = uu____4624;
                 FStar_Syntax_Syntax.vars = uu____4625;_} ->
                 let uu____4632 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____4632 with
                  | (b,f1) ->
                      let uu____4646 =
                        let uu____4647 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____4647 in
                      (uu____4646, f1))
             | uu____4652 -> failwith "impossible" in
           (match uu____4615 with
            | (x,f) ->
                let uu____4659 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4659 with
                 | (base_t,decls) ->
                     let uu____4666 = gen_term_var env x in
                     (match uu____4666 with
                      | (x1,xtm,env') ->
                          let uu____4675 = encode_formula f env' in
                          (match uu____4675 with
                           | (refinement,decls') ->
                               let uu____4682 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4682 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4693 =
                                        let uu____4695 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4699 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4695
                                          uu____4699 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4693 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4718  ->
                                              match uu____4718 with
                                              | (y,uu____4722) ->
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
                                    let uu____4741 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4741 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4746 =
                                           let uu____4747 =
                                             let uu____4751 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4751) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4747 in
                                         (uu____4746,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____4763 =
                                             let uu____4764 =
                                               let uu____4765 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4765 in
                                             Prims.strcat module_name
                                               uu____4764 in
                                           varops.mk_unique uu____4763 in
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
                                           let uu____4774 =
                                             let uu____4778 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4778) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4774 in
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
                                           let uu____4789 =
                                             let uu____4793 =
                                               let uu____4794 =
                                                 let uu____4800 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4800) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4794 in
                                             (uu____4793,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4789 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4815 =
                                             let uu____4819 =
                                               let uu____4820 =
                                                 let uu____4826 =
                                                   let uu____4827 =
                                                     let uu____4830 =
                                                       let uu____4831 =
                                                         let uu____4837 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4837) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4831 in
                                                     (uu____4830, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4827 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4826) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4820 in
                                             (uu____4819,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4815 in
                                         let t_kinding =
                                           let uu____4857 =
                                             let uu____4861 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4861,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4857 in
                                         let t_interp =
                                           let uu____4871 =
                                             let uu____4875 =
                                               let uu____4876 =
                                                 let uu____4882 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4882) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4876 in
                                             let uu____4894 =
                                               let uu____4896 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4896 in
                                             (uu____4875, uu____4894,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4871 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4901 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4901);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4922 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4922 in
           let uu____4923 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____4923 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4931 =
                    let uu____4935 =
                      let uu____4936 =
                        let uu____4937 =
                          let uu____4938 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4938 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4937 in
                      varops.mk_unique uu____4936 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4935) in
                  FStar_SMTEncoding_Util.mkAssume uu____4931 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4941 ->
           let uu____4951 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4951 with
            | (head1,args_e) ->
                let uu____4979 =
                  let uu____4987 =
                    let uu____4988 = FStar_Syntax_Subst.compress head1 in
                    uu____4988.FStar_Syntax_Syntax.n in
                  (uu____4987, args_e) in
                (match uu____4979 with
                 | uu____4998 when head_redex env head1 ->
                     let uu____5006 = whnf env t in
                     encode_term uu____5006 env
                 | uu____5007 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____5019 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____5028;
                       FStar_Syntax_Syntax.pos = uu____5029;
                       FStar_Syntax_Syntax.vars = uu____5030;_},uu____5031),uu____5032::
                    (v1,uu____5034)::(v2,uu____5036)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5074 = encode_term v1 env in
                     (match uu____5074 with
                      | (v11,decls1) ->
                          let uu____5081 = encode_term v2 env in
                          (match uu____5081 with
                           | (v21,decls2) ->
                               let uu____5088 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5088,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____5091::(v1,uu____5093)::(v2,uu____5095)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____5129 = encode_term v1 env in
                     (match uu____5129 with
                      | (v11,decls1) ->
                          let uu____5136 = encode_term v2 env in
                          (match uu____5136 with
                           | (v21,decls2) ->
                               let uu____5143 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____5143,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____5145) ->
                     let e0 =
                       let uu____5157 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____5157 in
                     ((let uu____5163 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____5163
                       then
                         let uu____5164 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____5164
                       else ());
                      (let e =
                         let uu____5169 =
                           let uu____5170 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____5171 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____5170
                             uu____5171 in
                         uu____5169 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____5180),(arg,uu____5182)::[]) -> encode_term arg env
                 | uu____5200 ->
                     let uu____5208 = encode_args args_e env in
                     (match uu____5208 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____5241 = encode_term head1 env in
                            match uu____5241 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____5280 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____5280 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____5330  ->
                                                 fun uu____5331  ->
                                                   match (uu____5330,
                                                           uu____5331)
                                                   with
                                                   | ((bv,uu____5345),
                                                      (a,uu____5347)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____5361 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____5361
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____5366 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____5366 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____5376 =
                                                   let uu____5380 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____5385 =
                                                     let uu____5386 =
                                                       let uu____5387 =
                                                         let uu____5388 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____5388 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____5387 in
                                                     varops.mk_unique
                                                       uu____5386 in
                                                   (uu____5380,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____5385) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____5376 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____5399 = lookup_free_var_sym env fv in
                            match uu____5399 with
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
                                   FStar_Syntax_Syntax.tk = uu____5420;
                                   FStar_Syntax_Syntax.pos = uu____5421;
                                   FStar_Syntax_Syntax.vars = uu____5422;_},uu____5423)
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
                                   FStar_Syntax_Syntax.tk = uu____5434;
                                   FStar_Syntax_Syntax.pos = uu____5435;
                                   FStar_Syntax_Syntax.vars = uu____5436;_},uu____5437)
                                ->
                                let uu____5442 =
                                  let uu____5443 =
                                    let uu____5446 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5446
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5443
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5442
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____5462 =
                                  let uu____5463 =
                                    let uu____5466 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____5466
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____5463
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____5462
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5481,(FStar_Util.Inl t1,uu____5483),uu____5484)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____5522,(FStar_Util.Inr c,uu____5524),uu____5525)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____5563 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____5583 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____5583 in
                               let uu____5584 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____5584 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____5594;
                                            FStar_Syntax_Syntax.pos =
                                              uu____5595;
                                            FStar_Syntax_Syntax.vars =
                                              uu____5596;_},uu____5597)
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
                                     | uu____5623 ->
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
           let uu____5663 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____5663 with
            | (bs1,body1,opening) ->
                let fallback uu____5678 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____5683 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____5683, [decl]) in
                let is_impure rc =
                  let uu____5689 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____5689 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5698 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5698
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____5711 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____5711
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____5714 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____5714)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5719 =
                         let uu____5720 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5720 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5719);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____5722 =
                       (is_impure rc) &&
                         (let uu____5724 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____5724) in
                     if uu____5722
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5729 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____5729 with
                        | (vars,guards,envbody,decls,uu____5744) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____5752 = encode_term body2 envbody in
                            (match uu____5752 with
                             | (body3,decls') ->
                                 let uu____5759 =
                                   let uu____5764 = codomain_eff rc in
                                   match uu____5764 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____5776 = encode_term tfun env in
                                       (match uu____5776 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____5759 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5795 =
                                          let uu____5801 =
                                            let uu____5802 =
                                              let uu____5805 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____5805, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5802 in
                                          ([], vars, uu____5801) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5795 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____5813 =
                                              let uu____5815 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____5815
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5813 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____5826 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____5826 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5831 =
                                             let uu____5832 =
                                               let uu____5836 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5836) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5832 in
                                           (uu____5831,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5842 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____5842 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5849 =
                                                    let uu____5850 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____5850 = cache_size in
                                                  if uu____5849
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
                                                    let uu____5861 =
                                                      let uu____5862 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5862 in
                                                    varops.mk_unique
                                                      uu____5861 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____5867 =
                                                    let uu____5871 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____5871) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5867 in
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
                                                      let uu____5883 =
                                                        let uu____5884 =
                                                          let uu____5888 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____5888,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5884 in
                                                      [uu____5883] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____5896 =
                                                    let uu____5900 =
                                                      let uu____5901 =
                                                        let uu____5907 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5907) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5901 in
                                                    (uu____5900,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5896 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____5917 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5917);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5919,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5920;
                          FStar_Syntax_Syntax.lbunivs = uu____5921;
                          FStar_Syntax_Syntax.lbtyp = uu____5922;
                          FStar_Syntax_Syntax.lbeff = uu____5923;
                          FStar_Syntax_Syntax.lbdef = uu____5924;_}::uu____5925),uu____5926)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5944;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5946;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5962 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____5975 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5975, [decl_e])))
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
              let uu____6015 = encode_term e1 env in
              match uu____6015 with
              | (ee1,decls1) ->
                  let uu____6022 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____6022 with
                   | (xs,e21) ->
                       let uu____6036 = FStar_List.hd xs in
                       (match uu____6036 with
                        | (x1,uu____6044) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____6046 = encode_body e21 env' in
                            (match uu____6046 with
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
            let uu____6068 =
              let uu____6072 =
                let uu____6073 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____6073 in
              gen_term_var env uu____6072 in
            match uu____6068 with
            | (scrsym,scr',env1) ->
                let uu____6083 = encode_term e env1 in
                (match uu____6083 with
                 | (scr,decls) ->
                     let uu____6090 =
                       let encode_branch b uu____6106 =
                         match uu____6106 with
                         | (else_case,decls1) ->
                             let uu____6117 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____6117 with
                              | (p,w,br) ->
                                  let uu____6136 = encode_pat env1 p in
                                  (match uu____6136 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____6160  ->
                                                   match uu____6160 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____6165 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____6180 =
                                               encode_term w1 env2 in
                                             (match uu____6180 with
                                              | (w2,decls2) ->
                                                  let uu____6188 =
                                                    let uu____6189 =
                                                      let uu____6192 =
                                                        let uu____6193 =
                                                          let uu____6196 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____6196) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____6193 in
                                                      (guard, uu____6192) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____6189 in
                                                  (uu____6188, decls2)) in
                                       (match uu____6165 with
                                        | (guard1,decls2) ->
                                            let uu____6204 =
                                              encode_br br env2 in
                                            (match uu____6204 with
                                             | (br1,decls3) ->
                                                 let uu____6212 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____6212,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____6090 with
                      | (match_tm,decls1) ->
                          let uu____6223 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____6223, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____6245 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____6245
       then
         let uu____6246 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____6246
       else ());
      (let uu____6248 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____6248 with
       | (vars,pat_term) ->
           let uu____6258 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____6289  ->
                     fun v1  ->
                       match uu____6289 with
                       | (env1,vars1) ->
                           let uu____6317 = gen_term_var env1 v1 in
                           (match uu____6317 with
                            | (xx,uu____6329,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____6258 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____6374 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____6375 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____6376 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____6382 =
                        let uu____6385 = encode_const c in
                        (scrutinee, uu____6385) in
                      FStar_SMTEncoding_Util.mkEq uu____6382
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____6398 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____6398 with
                        | (uu____6402,uu____6403::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____6405 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6426  ->
                                  match uu____6426 with
                                  | (arg,uu____6431) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____6435 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____6435)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____6453) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____6472 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____6485 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6511  ->
                                  match uu____6511 with
                                  | (arg,uu____6519) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____6523 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____6523)) in
                      FStar_All.pipe_right uu____6485 FStar_List.flatten in
                let pat_term1 uu____6539 = encode_term pat_term env1 in
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
      let uu____6546 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____6570  ->
                fun uu____6571  ->
                  match (uu____6570, uu____6571) with
                  | ((tms,decls),(t,uu____6591)) ->
                      let uu____6602 = encode_term t env in
                      (match uu____6602 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____6546 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____6636 = FStar_Syntax_Util.list_elements e in
        match uu____6636 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____6651 =
          let uu____6661 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____6661 FStar_Syntax_Util.head_and_args in
        match uu____6651 with
        | (head1,args) ->
            let uu____6689 =
              let uu____6697 =
                let uu____6698 = FStar_Syntax_Util.un_uinst head1 in
                uu____6698.FStar_Syntax_Syntax.n in
              (uu____6697, args) in
            (match uu____6689 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6709,uu____6710)::(e,uu____6712)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____6738 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6765 =
            let uu____6775 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6775 FStar_Syntax_Util.head_and_args in
          match uu____6765 with
          | (head1,args) ->
              let uu____6804 =
                let uu____6812 =
                  let uu____6813 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6813.FStar_Syntax_Syntax.n in
                (uu____6812, args) in
              (match uu____6804 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6826)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____6846 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____6861 = smt_pat_or1 t1 in
            (match uu____6861 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____6874 = list_elements1 e in
                 FStar_All.pipe_right uu____6874
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6887 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6887
                           (FStar_List.map one_pat)))
             | uu____6895 ->
                 let uu____6899 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6899])
        | uu____6915 ->
            let uu____6917 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6917] in
      let uu____6933 =
        let uu____6946 =
          let uu____6947 = FStar_Syntax_Subst.compress t in
          uu____6947.FStar_Syntax_Syntax.n in
        match uu____6946 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6974 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6974 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____7003;
                        FStar_Syntax_Syntax.effect_name = uu____7004;
                        FStar_Syntax_Syntax.result_typ = uu____7005;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____7007)::(post,uu____7009)::(pats,uu____7011)::[];
                        FStar_Syntax_Syntax.flags = uu____7012;_}
                      ->
                      let uu____7044 = lemma_pats pats in
                      (binders1, pre, post, uu____7044)
                  | uu____7057 -> failwith "impos"))
        | uu____7070 -> failwith "Impos" in
      match uu____6933 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_7106 = env in
            {
              bindings = (uu___136_7106.bindings);
              depth = (uu___136_7106.depth);
              tcenv = (uu___136_7106.tcenv);
              warn = (uu___136_7106.warn);
              cache = (uu___136_7106.cache);
              nolabels = (uu___136_7106.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_7106.encode_non_total_function_typ);
              current_module_name = (uu___136_7106.current_module_name)
            } in
          let uu____7107 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____7107 with
           | (vars,guards,env2,decls,uu____7122) ->
               let uu____7129 =
                 let uu____7136 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____7162 =
                             let uu____7167 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____7167 FStar_List.unzip in
                           match uu____7162 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____7136 FStar_List.unzip in
               (match uu____7129 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_7226 = env2 in
                      {
                        bindings = (uu___137_7226.bindings);
                        depth = (uu___137_7226.depth);
                        tcenv = (uu___137_7226.tcenv);
                        warn = (uu___137_7226.warn);
                        cache = (uu___137_7226.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_7226.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_7226.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_7226.current_module_name)
                      } in
                    let uu____7227 =
                      let uu____7230 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____7230 env3 in
                    (match uu____7227 with
                     | (pre1,decls'') ->
                         let uu____7235 =
                           let uu____7238 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____7238 env3 in
                         (match uu____7235 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____7245 =
                                let uu____7246 =
                                  let uu____7252 =
                                    let uu____7253 =
                                      let uu____7256 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____7256, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____7253 in
                                  (pats, vars, uu____7252) in
                                FStar_SMTEncoding_Util.mkForall uu____7246 in
                              (uu____7245, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____7269 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____7269
        then
          let uu____7270 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____7271 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____7270 uu____7271
        else () in
      let enc f r l =
        let uu____7298 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____7316 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____7316 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____7298 with
        | (decls,args) ->
            let uu____7333 =
              let uu___138_7334 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_7334.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_7334.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____7333, decls) in
      let const_op f r uu____7359 = let uu____7368 = f r in (uu____7368, []) in
      let un_op f l =
        let uu____7384 = FStar_List.hd l in FStar_All.pipe_left f uu____7384 in
      let bin_op f uu___112_7397 =
        match uu___112_7397 with
        | t1::t2::[] -> f (t1, t2)
        | uu____7405 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____7432 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____7448  ->
                 match uu____7448 with
                 | (t,uu____7456) ->
                     let uu____7457 = encode_formula t env in
                     (match uu____7457 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____7432 with
        | (decls,phis) ->
            let uu____7474 =
              let uu___139_7475 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_7475.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_7475.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____7474, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____7518  ->
               match uu____7518 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____7532) -> false
                    | uu____7533 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____7546 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____7546
        else
          (let uu____7561 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____7561 r rf) in
      let mk_imp1 r uu___113_7580 =
        match uu___113_7580 with
        | (lhs,uu____7584)::(rhs,uu____7586)::[] ->
            let uu____7607 = encode_formula rhs env in
            (match uu____7607 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____7616) ->
                      (l1, decls1)
                  | uu____7619 ->
                      let uu____7620 = encode_formula lhs env in
                      (match uu____7620 with
                       | (l2,decls2) ->
                           let uu____7627 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____7627, (FStar_List.append decls1 decls2)))))
        | uu____7629 -> failwith "impossible" in
      let mk_ite r uu___114_7644 =
        match uu___114_7644 with
        | (guard,uu____7648)::(_then,uu____7650)::(_else,uu____7652)::[] ->
            let uu____7681 = encode_formula guard env in
            (match uu____7681 with
             | (g,decls1) ->
                 let uu____7688 = encode_formula _then env in
                 (match uu____7688 with
                  | (t,decls2) ->
                      let uu____7695 = encode_formula _else env in
                      (match uu____7695 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7704 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7723 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7723 in
      let connectives =
        let uu____7735 =
          let uu____7744 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____7744) in
        let uu____7757 =
          let uu____7767 =
            let uu____7776 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____7776) in
          let uu____7789 =
            let uu____7799 =
              let uu____7809 =
                let uu____7818 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____7818) in
              let uu____7831 =
                let uu____7841 =
                  let uu____7851 =
                    let uu____7860 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____7860) in
                  [uu____7851;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____7841 in
              uu____7809 :: uu____7831 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____7799 in
          uu____7767 :: uu____7789 in
        uu____7735 :: uu____7757 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____8076 = encode_formula phi' env in
            (match uu____8076 with
             | (phi2,decls) ->
                 let uu____8083 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____8083, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____8084 ->
            let uu____8089 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____8089 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____8116 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____8116 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____8124;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____8126;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____8142 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____8142 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____8174::(x,uu____8176)::(t,uu____8178)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____8212 = encode_term x env in
                 (match uu____8212 with
                  | (x1,decls) ->
                      let uu____8219 = encode_term t env in
                      (match uu____8219 with
                       | (t1,decls') ->
                           let uu____8226 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____8226, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____8230)::(msg,uu____8232)::(phi2,uu____8234)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____8268 =
                   let uu____8271 =
                     let uu____8272 = FStar_Syntax_Subst.compress r in
                     uu____8272.FStar_Syntax_Syntax.n in
                   let uu____8275 =
                     let uu____8276 = FStar_Syntax_Subst.compress msg in
                     uu____8276.FStar_Syntax_Syntax.n in
                   (uu____8271, uu____8275) in
                 (match uu____8268 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____8283))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____8295 -> fallback phi2)
             | uu____8298 when head_redex env head2 ->
                 let uu____8306 = whnf env phi1 in
                 encode_formula uu____8306 env
             | uu____8307 ->
                 let uu____8315 = encode_term phi1 env in
                 (match uu____8315 with
                  | (tt,decls) ->
                      let uu____8322 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_8325 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_8325.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_8325.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____8322, decls)))
        | uu____8328 ->
            let uu____8329 = encode_term phi1 env in
            (match uu____8329 with
             | (tt,decls) ->
                 let uu____8336 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_8339 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_8339.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_8339.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____8336, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____8366 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____8366 with
        | (vars,guards,env2,decls,uu____8388) ->
            let uu____8395 =
              let uu____8402 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____8429 =
                          let uu____8434 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____8451  ->
                                    match uu____8451 with
                                    | (t,uu____8457) ->
                                        encode_term t
                                          (let uu___142_8459 = env2 in
                                           {
                                             bindings =
                                               (uu___142_8459.bindings);
                                             depth = (uu___142_8459.depth);
                                             tcenv = (uu___142_8459.tcenv);
                                             warn = (uu___142_8459.warn);
                                             cache = (uu___142_8459.cache);
                                             nolabels =
                                               (uu___142_8459.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_8459.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_8459.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____8434 FStar_List.unzip in
                        match uu____8429 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____8402 FStar_List.unzip in
            (match uu____8395 with
             | (pats,decls') ->
                 let uu____8511 = encode_formula body env2 in
                 (match uu____8511 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____8530;
                             FStar_SMTEncoding_Term.rng = uu____8531;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____8539 -> guards in
                      let uu____8542 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____8542, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____8579  ->
                   match uu____8579 with
                   | (x,uu____8583) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____8589 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____8598 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____8598) uu____8589 tl1 in
             let uu____8600 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____8616  ->
                       match uu____8616 with
                       | (b,uu____8620) ->
                           let uu____8621 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____8621)) in
             (match uu____8600 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____8625) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____8637 =
                    let uu____8638 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____8638 in
                  FStar_Errors.warn pos uu____8637) in
       let uu____8639 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____8639 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____8645 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____8684  ->
                     match uu____8684 with
                     | (l,uu____8694) -> FStar_Ident.lid_equals op l)) in
           (match uu____8645 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____8717,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8746 = encode_q_body env vars pats body in
             match uu____8746 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8772 =
                     let uu____8778 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8778) in
                   FStar_SMTEncoding_Term.mkForall uu____8772
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8790 = encode_q_body env vars pats body in
             match uu____8790 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8815 =
                   let uu____8816 =
                     let uu____8822 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8822) in
                   FStar_SMTEncoding_Term.mkExists uu____8816
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8815, decls))))
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
  let uu____8901 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8901 with
  | (asym,a) ->
      let uu____8906 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8906 with
       | (xsym,x) ->
           let uu____8911 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8911 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8941 =
                      let uu____8947 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____8947, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8941 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____8962 =
                      let uu____8966 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8966) in
                    FStar_SMTEncoding_Util.mkApp uu____8962 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8974 =
                    let uu____8976 =
                      let uu____8978 =
                        let uu____8980 =
                          let uu____8981 =
                            let uu____8985 =
                              let uu____8986 =
                                let uu____8992 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8992) in
                              FStar_SMTEncoding_Util.mkForall uu____8986 in
                            (uu____8985, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8981 in
                        let uu____9001 =
                          let uu____9003 =
                            let uu____9004 =
                              let uu____9008 =
                                let uu____9009 =
                                  let uu____9015 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____9015) in
                                FStar_SMTEncoding_Util.mkForall uu____9009 in
                              (uu____9008,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____9004 in
                          [uu____9003] in
                        uu____8980 :: uu____9001 in
                      xtok_decl :: uu____8978 in
                    xname_decl :: uu____8976 in
                  (xtok1, uu____8974) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____9064 =
                    let uu____9072 =
                      let uu____9078 =
                        let uu____9079 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____9079 in
                      quant axy uu____9078 in
                    (FStar_Parser_Const.op_Eq, uu____9072) in
                  let uu____9085 =
                    let uu____9094 =
                      let uu____9102 =
                        let uu____9108 =
                          let uu____9109 =
                            let uu____9110 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____9110 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____9109 in
                        quant axy uu____9108 in
                      (FStar_Parser_Const.op_notEq, uu____9102) in
                    let uu____9116 =
                      let uu____9125 =
                        let uu____9133 =
                          let uu____9139 =
                            let uu____9140 =
                              let uu____9141 =
                                let uu____9144 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9145 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____9144, uu____9145) in
                              FStar_SMTEncoding_Util.mkLT uu____9141 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____9140 in
                          quant xy uu____9139 in
                        (FStar_Parser_Const.op_LT, uu____9133) in
                      let uu____9151 =
                        let uu____9160 =
                          let uu____9168 =
                            let uu____9174 =
                              let uu____9175 =
                                let uu____9176 =
                                  let uu____9179 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____9180 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____9179, uu____9180) in
                                FStar_SMTEncoding_Util.mkLTE uu____9176 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____9175 in
                            quant xy uu____9174 in
                          (FStar_Parser_Const.op_LTE, uu____9168) in
                        let uu____9186 =
                          let uu____9195 =
                            let uu____9203 =
                              let uu____9209 =
                                let uu____9210 =
                                  let uu____9211 =
                                    let uu____9214 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____9215 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____9214, uu____9215) in
                                  FStar_SMTEncoding_Util.mkGT uu____9211 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____9210 in
                              quant xy uu____9209 in
                            (FStar_Parser_Const.op_GT, uu____9203) in
                          let uu____9221 =
                            let uu____9230 =
                              let uu____9238 =
                                let uu____9244 =
                                  let uu____9245 =
                                    let uu____9246 =
                                      let uu____9249 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____9250 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____9249, uu____9250) in
                                    FStar_SMTEncoding_Util.mkGTE uu____9246 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____9245 in
                                quant xy uu____9244 in
                              (FStar_Parser_Const.op_GTE, uu____9238) in
                            let uu____9256 =
                              let uu____9265 =
                                let uu____9273 =
                                  let uu____9279 =
                                    let uu____9280 =
                                      let uu____9281 =
                                        let uu____9284 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____9285 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____9284, uu____9285) in
                                      FStar_SMTEncoding_Util.mkSub uu____9281 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____9280 in
                                  quant xy uu____9279 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____9273) in
                              let uu____9291 =
                                let uu____9300 =
                                  let uu____9308 =
                                    let uu____9314 =
                                      let uu____9315 =
                                        let uu____9316 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____9316 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____9315 in
                                    quant qx uu____9314 in
                                  (FStar_Parser_Const.op_Minus, uu____9308) in
                                let uu____9322 =
                                  let uu____9331 =
                                    let uu____9339 =
                                      let uu____9345 =
                                        let uu____9346 =
                                          let uu____9347 =
                                            let uu____9350 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____9351 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____9350, uu____9351) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____9347 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____9346 in
                                      quant xy uu____9345 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____9339) in
                                  let uu____9357 =
                                    let uu____9366 =
                                      let uu____9374 =
                                        let uu____9380 =
                                          let uu____9381 =
                                            let uu____9382 =
                                              let uu____9385 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____9386 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____9385, uu____9386) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____9382 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____9381 in
                                        quant xy uu____9380 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____9374) in
                                    let uu____9392 =
                                      let uu____9401 =
                                        let uu____9409 =
                                          let uu____9415 =
                                            let uu____9416 =
                                              let uu____9417 =
                                                let uu____9420 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____9421 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____9420, uu____9421) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____9417 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____9416 in
                                          quant xy uu____9415 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____9409) in
                                      let uu____9427 =
                                        let uu____9436 =
                                          let uu____9444 =
                                            let uu____9450 =
                                              let uu____9451 =
                                                let uu____9452 =
                                                  let uu____9455 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____9456 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____9455, uu____9456) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____9452 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____9451 in
                                            quant xy uu____9450 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____9444) in
                                        let uu____9462 =
                                          let uu____9471 =
                                            let uu____9479 =
                                              let uu____9485 =
                                                let uu____9486 =
                                                  let uu____9487 =
                                                    let uu____9490 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____9491 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____9490, uu____9491) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____9487 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____9486 in
                                              quant xy uu____9485 in
                                            (FStar_Parser_Const.op_And,
                                              uu____9479) in
                                          let uu____9497 =
                                            let uu____9506 =
                                              let uu____9514 =
                                                let uu____9520 =
                                                  let uu____9521 =
                                                    let uu____9522 =
                                                      let uu____9525 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____9526 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____9525,
                                                        uu____9526) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____9522 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____9521 in
                                                quant xy uu____9520 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____9514) in
                                            let uu____9532 =
                                              let uu____9541 =
                                                let uu____9549 =
                                                  let uu____9555 =
                                                    let uu____9556 =
                                                      let uu____9557 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____9557 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____9556 in
                                                  quant qx uu____9555 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____9549) in
                                              [uu____9541] in
                                            uu____9506 :: uu____9532 in
                                          uu____9471 :: uu____9497 in
                                        uu____9436 :: uu____9462 in
                                      uu____9401 :: uu____9427 in
                                    uu____9366 :: uu____9392 in
                                  uu____9331 :: uu____9357 in
                                uu____9300 :: uu____9322 in
                              uu____9265 :: uu____9291 in
                            uu____9230 :: uu____9256 in
                          uu____9195 :: uu____9221 in
                        uu____9160 :: uu____9186 in
                      uu____9125 :: uu____9151 in
                    uu____9094 :: uu____9116 in
                  uu____9064 :: uu____9085 in
                let mk1 l v1 =
                  let uu____9685 =
                    let uu____9690 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9725  ->
                              match uu____9725 with
                              | (l',uu____9734) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____9690
                      (FStar_Option.map
                         (fun uu____9770  ->
                            match uu____9770 with | (uu____9781,b) -> b v1)) in
                  FStar_All.pipe_right uu____9685 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9825  ->
                          match uu____9825 with
                          | (l',uu____9834) -> FStar_Ident.lid_equals l l')) in
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
        let uu____9863 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9863 with
        | (xxsym,xx) ->
            let uu____9868 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9868 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____9876 =
                   let uu____9880 =
                     let uu____9881 =
                       let uu____9887 =
                         let uu____9888 =
                           let uu____9891 =
                             let uu____9892 =
                               let uu____9895 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9895) in
                             FStar_SMTEncoding_Util.mkEq uu____9892 in
                           (xx_has_type, uu____9891) in
                         FStar_SMTEncoding_Util.mkImp uu____9888 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9887) in
                     FStar_SMTEncoding_Util.mkForall uu____9881 in
                   let uu____9908 =
                     let uu____9909 =
                       let uu____9910 =
                         let uu____9911 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9911 in
                       Prims.strcat module_name uu____9910 in
                     varops.mk_unique uu____9909 in
                   (uu____9880, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____9908) in
                 FStar_SMTEncoding_Util.mkAssume uu____9876)
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
    let uu____9945 =
      let uu____9946 =
        let uu____9950 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9950, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9946 in
    let uu____9952 =
      let uu____9954 =
        let uu____9955 =
          let uu____9959 =
            let uu____9960 =
              let uu____9966 =
                let uu____9967 =
                  let uu____9970 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9970) in
                FStar_SMTEncoding_Util.mkImp uu____9967 in
              ([[typing_pred]], [xx], uu____9966) in
            mkForall_fuel uu____9960 in
          (uu____9959, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9955 in
      [uu____9954] in
    uu____9945 :: uu____9952 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9998 =
      let uu____9999 =
        let uu____10003 =
          let uu____10004 =
            let uu____10010 =
              let uu____10013 =
                let uu____10015 = FStar_SMTEncoding_Term.boxBool b in
                [uu____10015] in
              [uu____10013] in
            let uu____10018 =
              let uu____10019 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____10019 tt in
            (uu____10010, [bb], uu____10018) in
          FStar_SMTEncoding_Util.mkForall uu____10004 in
        (uu____10003, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9999 in
    let uu____10030 =
      let uu____10032 =
        let uu____10033 =
          let uu____10037 =
            let uu____10038 =
              let uu____10044 =
                let uu____10045 =
                  let uu____10048 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____10048) in
                FStar_SMTEncoding_Util.mkImp uu____10045 in
              ([[typing_pred]], [xx], uu____10044) in
            mkForall_fuel uu____10038 in
          (uu____10037, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____10033 in
      [uu____10032] in
    uu____9998 :: uu____10030 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____10082 =
        let uu____10083 =
          let uu____10087 =
            let uu____10089 =
              let uu____10091 =
                let uu____10093 = FStar_SMTEncoding_Term.boxInt a in
                let uu____10094 =
                  let uu____10096 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____10096] in
                uu____10093 :: uu____10094 in
              tt :: uu____10091 in
            tt :: uu____10089 in
          ("Prims.Precedes", uu____10087) in
        FStar_SMTEncoding_Util.mkApp uu____10083 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____10082 in
    let precedes_y_x =
      let uu____10099 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____10099 in
    let uu____10101 =
      let uu____10102 =
        let uu____10106 =
          let uu____10107 =
            let uu____10113 =
              let uu____10116 =
                let uu____10118 = FStar_SMTEncoding_Term.boxInt b in
                [uu____10118] in
              [uu____10116] in
            let uu____10121 =
              let uu____10122 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____10122 tt in
            (uu____10113, [bb], uu____10121) in
          FStar_SMTEncoding_Util.mkForall uu____10107 in
        (uu____10106, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____10102 in
    let uu____10133 =
      let uu____10135 =
        let uu____10136 =
          let uu____10140 =
            let uu____10141 =
              let uu____10147 =
                let uu____10148 =
                  let uu____10151 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____10151) in
                FStar_SMTEncoding_Util.mkImp uu____10148 in
              ([[typing_pred]], [xx], uu____10147) in
            mkForall_fuel uu____10141 in
          (uu____10140, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____10136 in
      let uu____10164 =
        let uu____10166 =
          let uu____10167 =
            let uu____10171 =
              let uu____10172 =
                let uu____10178 =
                  let uu____10179 =
                    let uu____10182 =
                      let uu____10183 =
                        let uu____10185 =
                          let uu____10187 =
                            let uu____10189 =
                              let uu____10190 =
                                let uu____10193 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____10194 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____10193, uu____10194) in
                              FStar_SMTEncoding_Util.mkGT uu____10190 in
                            let uu____10195 =
                              let uu____10197 =
                                let uu____10198 =
                                  let uu____10201 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____10202 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____10201, uu____10202) in
                                FStar_SMTEncoding_Util.mkGTE uu____10198 in
                              let uu____10203 =
                                let uu____10205 =
                                  let uu____10206 =
                                    let uu____10209 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____10210 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____10209, uu____10210) in
                                  FStar_SMTEncoding_Util.mkLT uu____10206 in
                                [uu____10205] in
                              uu____10197 :: uu____10203 in
                            uu____10189 :: uu____10195 in
                          typing_pred_y :: uu____10187 in
                        typing_pred :: uu____10185 in
                      FStar_SMTEncoding_Util.mk_and_l uu____10183 in
                    (uu____10182, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____10179 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____10178) in
              mkForall_fuel uu____10172 in
            (uu____10171,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____10167 in
        [uu____10166] in
      uu____10135 :: uu____10164 in
    uu____10101 :: uu____10133 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____10240 =
      let uu____10241 =
        let uu____10245 =
          let uu____10246 =
            let uu____10252 =
              let uu____10255 =
                let uu____10257 = FStar_SMTEncoding_Term.boxString b in
                [uu____10257] in
              [uu____10255] in
            let uu____10260 =
              let uu____10261 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____10261 tt in
            (uu____10252, [bb], uu____10260) in
          FStar_SMTEncoding_Util.mkForall uu____10246 in
        (uu____10245, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____10241 in
    let uu____10272 =
      let uu____10274 =
        let uu____10275 =
          let uu____10279 =
            let uu____10280 =
              let uu____10286 =
                let uu____10287 =
                  let uu____10290 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____10290) in
                FStar_SMTEncoding_Util.mkImp uu____10287 in
              ([[typing_pred]], [xx], uu____10286) in
            mkForall_fuel uu____10280 in
          (uu____10279, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____10275 in
      [uu____10274] in
    uu____10240 :: uu____10272 in
  let mk_ref1 env reft_name uu____10312 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____10323 =
        let uu____10327 =
          let uu____10329 = FStar_SMTEncoding_Util.mkFreeV aa in
          [uu____10329] in
        (reft_name, uu____10327) in
      FStar_SMTEncoding_Util.mkApp uu____10323 in
    let refb =
      let uu____10332 =
        let uu____10336 =
          let uu____10338 = FStar_SMTEncoding_Util.mkFreeV bb in
          [uu____10338] in
        (reft_name, uu____10336) in
      FStar_SMTEncoding_Util.mkApp uu____10332 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____10342 =
      let uu____10343 =
        let uu____10347 =
          let uu____10348 =
            let uu____10354 =
              let uu____10355 =
                let uu____10358 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____10358) in
              FStar_SMTEncoding_Util.mkImp uu____10355 in
            ([[typing_pred]], [xx; aa], uu____10354) in
          mkForall_fuel uu____10348 in
        (uu____10347, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____10343 in
    [uu____10342] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____10398 =
      let uu____10399 =
        let uu____10403 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____10403, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10399 in
    [uu____10398] in
  let mk_and_interp env conj uu____10414 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10431 =
      let uu____10432 =
        let uu____10436 =
          let uu____10437 =
            let uu____10443 =
              let uu____10444 =
                let uu____10447 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____10447, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10444 in
            ([[l_and_a_b]], [aa; bb], uu____10443) in
          FStar_SMTEncoding_Util.mkForall uu____10437 in
        (uu____10436, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10432 in
    [uu____10431] in
  let mk_or_interp env disj uu____10471 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10488 =
      let uu____10489 =
        let uu____10493 =
          let uu____10494 =
            let uu____10500 =
              let uu____10501 =
                let uu____10504 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____10504, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10501 in
            ([[l_or_a_b]], [aa; bb], uu____10500) in
          FStar_SMTEncoding_Util.mkForall uu____10494 in
        (uu____10493, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10489 in
    [uu____10488] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____10545 =
      let uu____10546 =
        let uu____10550 =
          let uu____10551 =
            let uu____10557 =
              let uu____10558 =
                let uu____10561 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10561, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10558 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____10557) in
          FStar_SMTEncoding_Util.mkForall uu____10551 in
        (uu____10550, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10546 in
    [uu____10545] in
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
    let uu____10608 =
      let uu____10609 =
        let uu____10613 =
          let uu____10614 =
            let uu____10620 =
              let uu____10621 =
                let uu____10624 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10624, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10621 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____10620) in
          FStar_SMTEncoding_Util.mkForall uu____10614 in
        (uu____10613, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10609 in
    [uu____10608] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10669 =
      let uu____10670 =
        let uu____10674 =
          let uu____10675 =
            let uu____10681 =
              let uu____10682 =
                let uu____10685 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____10685, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10682 in
            ([[l_imp_a_b]], [aa; bb], uu____10681) in
          FStar_SMTEncoding_Util.mkForall uu____10675 in
        (uu____10674, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10670 in
    [uu____10669] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10726 =
      let uu____10727 =
        let uu____10731 =
          let uu____10732 =
            let uu____10738 =
              let uu____10739 =
                let uu____10742 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10742, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10739 in
            ([[l_iff_a_b]], [aa; bb], uu____10738) in
          FStar_SMTEncoding_Util.mkForall uu____10732 in
        (uu____10731, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10727 in
    [uu____10726] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____10776 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10776 in
    let uu____10778 =
      let uu____10779 =
        let uu____10783 =
          let uu____10784 =
            let uu____10790 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10790) in
          FStar_SMTEncoding_Util.mkForall uu____10784 in
        (uu____10783, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10779 in
    [uu____10778] in
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
      let uu____10830 =
        let uu____10834 =
          let uu____10836 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10836] in
        ("Valid", uu____10834) in
      FStar_SMTEncoding_Util.mkApp uu____10830 in
    let uu____10838 =
      let uu____10839 =
        let uu____10843 =
          let uu____10844 =
            let uu____10850 =
              let uu____10851 =
                let uu____10854 =
                  let uu____10855 =
                    let uu____10861 =
                      let uu____10864 =
                        let uu____10866 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10866] in
                      [uu____10864] in
                    let uu____10869 =
                      let uu____10870 =
                        let uu____10873 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10873, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10870 in
                    (uu____10861, [xx1], uu____10869) in
                  FStar_SMTEncoding_Util.mkForall uu____10855 in
                (uu____10854, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10851 in
            ([[l_forall_a_b]], [aa; bb], uu____10850) in
          FStar_SMTEncoding_Util.mkForall uu____10844 in
        (uu____10843, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10839 in
    [uu____10838] in
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
      let uu____10924 =
        let uu____10928 =
          let uu____10930 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10930] in
        ("Valid", uu____10928) in
      FStar_SMTEncoding_Util.mkApp uu____10924 in
    let uu____10932 =
      let uu____10933 =
        let uu____10937 =
          let uu____10938 =
            let uu____10944 =
              let uu____10945 =
                let uu____10948 =
                  let uu____10949 =
                    let uu____10955 =
                      let uu____10958 =
                        let uu____10960 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10960] in
                      [uu____10958] in
                    let uu____10963 =
                      let uu____10964 =
                        let uu____10967 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10967, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10964 in
                    (uu____10955, [xx1], uu____10963) in
                  FStar_SMTEncoding_Util.mkExists uu____10949 in
                (uu____10948, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10945 in
            ([[l_exists_a_b]], [aa; bb], uu____10944) in
          FStar_SMTEncoding_Util.mkForall uu____10938 in
        (uu____10937, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10933 in
    [uu____10932] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____11003 =
      let uu____11004 =
        let uu____11008 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____11009 = varops.mk_unique "typing_range_const" in
        (uu____11008, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____11009) in
      FStar_SMTEncoding_Util.mkAssume uu____11004 in
    [uu____11003] in
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
          let uu____11271 =
            FStar_Util.find_opt
              (fun uu____11292  ->
                 match uu____11292 with
                 | (l,uu____11302) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____11271 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____11324,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____11360 = encode_function_type_as_formula t env in
        match uu____11360 with
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
            let uu____11393 =
              (let uu____11396 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____11396) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____11393
            then
              let uu____11400 = new_term_constant_and_tok_from_lid env lid in
              match uu____11400 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____11412 =
                      let uu____11413 = FStar_Syntax_Subst.compress t_norm in
                      uu____11413.FStar_Syntax_Syntax.n in
                    match uu____11412 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____11418) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____11436  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____11439 -> [] in
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
              (let uu____11448 = prims.is lid in
               if uu____11448
               then
                 let vname = varops.new_fvar lid in
                 let uu____11453 = prims.mk lid vname in
                 match uu____11453 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____11468 =
                    let uu____11474 = curried_arrow_formals_comp t_norm in
                    match uu____11474 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____11485 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____11485
                          then
                            let uu____11486 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_11489 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_11489.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_11489.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_11489.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_11489.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_11489.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_11489.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_11489.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_11489.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_11489.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_11489.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_11489.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_11489.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_11489.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_11489.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_11489.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_11489.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_11489.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_11489.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_11489.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_11489.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_11489.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_11489.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_11489.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_11489.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_11489.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_11489.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____11486
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____11496 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____11496)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____11468 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____11523 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____11523 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____11536 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_11568  ->
                                     match uu___115_11568 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____11571 =
                                           FStar_Util.prefix vars in
                                         (match uu____11571 with
                                          | (uu____11582,(xxsym,uu____11584))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____11594 =
                                                let uu____11595 =
                                                  let uu____11599 =
                                                    let uu____11600 =
                                                      let uu____11606 =
                                                        let uu____11607 =
                                                          let uu____11610 =
                                                            let uu____11611 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____11611 in
                                                          (vapp, uu____11610) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____11607 in
                                                      ([[vapp]], vars,
                                                        uu____11606) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11600 in
                                                  (uu____11599,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11595 in
                                              [uu____11594])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____11622 =
                                           FStar_Util.prefix vars in
                                         (match uu____11622 with
                                          | (uu____11633,(xxsym,uu____11635))
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
                                              let uu____11649 =
                                                let uu____11650 =
                                                  let uu____11654 =
                                                    let uu____11655 =
                                                      let uu____11661 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____11661) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11655 in
                                                  (uu____11654,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11650 in
                                              [uu____11649])
                                     | uu____11670 -> [])) in
                           let uu____11671 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____11671 with
                            | (vars,guards,env',decls1,uu____11687) ->
                                let uu____11694 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____11699 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____11699, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____11701 = encode_formula p env' in
                                      (match uu____11701 with
                                       | (g,ds) ->
                                           let uu____11708 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____11708,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____11694 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____11717 =
                                         let uu____11721 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____11721) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____11717 in
                                     let uu____11726 =
                                       let vname_decl =
                                         let uu____11731 =
                                           let uu____11737 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11743  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11737,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____11731 in
                                       let uu____11748 =
                                         let env2 =
                                           let uu___144_11752 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11752.bindings);
                                             depth = (uu___144_11752.depth);
                                             tcenv = (uu___144_11752.tcenv);
                                             warn = (uu___144_11752.warn);
                                             cache = (uu___144_11752.cache);
                                             nolabels =
                                               (uu___144_11752.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11752.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11752.current_module_name)
                                           } in
                                         let uu____11753 =
                                           let uu____11754 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11754 in
                                         if uu____11753
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____11748 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11764::uu____11765 ->
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
                                                   let uu____11788 =
                                                     let uu____11794 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11794) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11788 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11808 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____11810 =
                                             match formals with
                                             | [] ->
                                                 let uu____11819 =
                                                   let uu____11820 =
                                                     let uu____11822 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_41)
                                                       uu____11822 in
                                                   push_free_var env1 lid
                                                     vname uu____11820 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11819)
                                             | uu____11825 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____11830 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11830 in
                                                 let name_tok_corr =
                                                   let uu____11832 =
                                                     let uu____11836 =
                                                       let uu____11837 =
                                                         let uu____11843 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11843) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11837 in
                                                     (uu____11836,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11832 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____11810 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____11726 with
                                      | (decls2,env2) ->
                                          let uu____11867 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11872 =
                                              encode_term res_t1 env' in
                                            match uu____11872 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11880 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11880,
                                                  decls) in
                                          (match uu____11867 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11888 =
                                                   let uu____11892 =
                                                     let uu____11893 =
                                                       let uu____11899 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11899) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11893 in
                                                   (uu____11892,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11888 in
                                               let freshness =
                                                 let uu____11908 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11908
                                                 then
                                                   let uu____11911 =
                                                     let uu____11912 =
                                                       let uu____11918 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____11924 =
                                                         varops.next_id () in
                                                       (vname, uu____11918,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11924) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11912 in
                                                   let uu____11926 =
                                                     let uu____11928 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11928] in
                                                   uu____11911 :: uu____11926
                                                 else [] in
                                               let g =
                                                 let uu____11932 =
                                                   let uu____11934 =
                                                     let uu____11936 =
                                                       let uu____11938 =
                                                         let uu____11940 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____11940 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11938 in
                                                     FStar_List.append decls3
                                                       uu____11936 in
                                                   FStar_List.append decls2
                                                     uu____11934 in
                                                 FStar_List.append decls11
                                                   uu____11932 in
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
          let uu____11966 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11966 with
          | FStar_Pervasives_Native.None  ->
              let uu____11985 = encode_free_var env x t t_norm [] in
              (match uu____11985 with
               | (decls,env1) ->
                   let uu____12000 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____12000 with
                    | (n1,x',uu____12015) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____12027) ->
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
          let uu____12064 = encode_free_var env lid t tt quals in
          match uu____12064 with
          | (decls,env1) ->
              let uu____12075 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____12075
              then
                let uu____12079 =
                  let uu____12081 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____12081 in
                (uu____12079, env1)
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
             (fun uu____12119  ->
                fun lb  ->
                  match uu____12119 with
                  | (decls,env1) ->
                      let uu____12131 =
                        let uu____12135 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____12135
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____12131 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____12150 = FStar_Syntax_Util.head_and_args t in
    match uu____12150 with
    | (hd1,args) ->
        let uu____12176 =
          let uu____12177 = FStar_Syntax_Util.un_uinst hd1 in
          uu____12177.FStar_Syntax_Syntax.n in
        (match uu____12176 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____12181,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____12194 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____12212  ->
      fun quals  ->
        match uu____12212 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____12262 = FStar_Util.first_N nbinders formals in
              match uu____12262 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____12311  ->
                         fun uu____12312  ->
                           match (uu____12311, uu____12312) with
                           | ((formal,uu____12322),(binder,uu____12324)) ->
                               let uu____12329 =
                                 let uu____12334 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____12334) in
                               FStar_Syntax_Syntax.NT uu____12329) formals1
                      binders in
                  let extra_formals1 =
                    let uu____12339 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____12357  ->
                              match uu____12357 with
                              | (x,i) ->
                                  let uu____12364 =
                                    let uu___145_12365 = x in
                                    let uu____12366 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_12365.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_12365.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____12366
                                    } in
                                  (uu____12364, i))) in
                    FStar_All.pipe_right uu____12339
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____12378 =
                      let uu____12380 =
                        let uu____12381 = FStar_Syntax_Subst.subst subst1 t in
                        uu____12381.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                        uu____12380 in
                    let uu____12385 =
                      let uu____12386 = FStar_Syntax_Subst.compress body in
                      let uu____12387 =
                        let uu____12388 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____12388 in
                      FStar_Syntax_Syntax.extend_app_n uu____12386
                        uu____12387 in
                    uu____12385 uu____12378 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____12430 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____12430
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_12433 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_12433.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_12433.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_12433.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_12433.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_12433.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_12433.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_12433.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_12433.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_12433.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_12433.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_12433.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_12433.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_12433.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_12433.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_12433.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_12433.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_12433.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_12433.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_12433.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_12433.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_12433.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_12433.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_12433.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_12433.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_12433.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_12433.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____12454 = FStar_Syntax_Util.abs_formals e in
                match uu____12454 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____12488::uu____12489 ->
                         let uu____12497 =
                           let uu____12498 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12498.FStar_Syntax_Syntax.n in
                         (match uu____12497 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12525 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12525 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____12553 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____12553
                                   then
                                     let uu____12576 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____12576 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____12631  ->
                                                   fun uu____12632  ->
                                                     match (uu____12631,
                                                             uu____12632)
                                                     with
                                                     | ((x,uu____12642),
                                                        (b,uu____12644)) ->
                                                         let uu____12649 =
                                                           let uu____12654 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____12654) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____12649)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____12656 =
                                            let uu____12667 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____12667) in
                                          (uu____12656, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____12707 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____12707 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12759) ->
                              let uu____12764 =
                                let uu____12775 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____12775 in
                              (uu____12764, true)
                          | uu____12808 when Prims.op_Negation norm1 ->
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
                          | uu____12810 ->
                              let uu____12811 =
                                let uu____12812 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12813 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12812
                                  uu____12813 in
                              failwith uu____12811)
                     | uu____12826 ->
                         let uu____12827 =
                           let uu____12828 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12828.FStar_Syntax_Syntax.n in
                         (match uu____12827 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12855 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12855 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12873 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12873 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12921 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12951 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____12951
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12959 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____13013  ->
                            fun lb  ->
                              match uu____13013 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____13064 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____13064
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____13067 =
                                      let uu____13075 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____13075
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____13067 with
                                    | (tok,decl,env2) ->
                                        let uu____13100 =
                                          let uu____13107 =
                                            let uu____13113 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____13113, tok) in
                                          uu____13107 :: toks in
                                        (uu____13100, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12959 with
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
                        | uu____13215 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____13220 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____13220 vars)
                            else
                              (let uu____13222 =
                                 let uu____13226 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____13226) in
                               FStar_SMTEncoding_Util.mkApp uu____13222) in
                      let uu____13231 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_13234  ->
                                 match uu___116_13234 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____13235 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____13240 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____13240))) in
                      if uu____13231
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____13260;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____13262;
                                FStar_Syntax_Syntax.lbeff = uu____13263;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____13300 =
                                 let uu____13304 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____13304 with
                                 | (tcenv',uu____13315,e_t) ->
                                     let uu____13319 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____13326 -> failwith "Impossible" in
                                     (match uu____13319 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_13336 = env1 in
                                            {
                                              bindings =
                                                (uu___149_13336.bindings);
                                              depth = (uu___149_13336.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_13336.warn);
                                              cache = (uu___149_13336.cache);
                                              nolabels =
                                                (uu___149_13336.nolabels);
                                              use_zfuel_name =
                                                (uu___149_13336.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_13336.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_13336.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____13300 with
                                | (env',e1,t_norm1) ->
                                    let uu____13343 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____13343 with
                                     | ((binders,body,uu____13355,uu____13356),curry)
                                         ->
                                         ((let uu____13363 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____13363
                                           then
                                             let uu____13364 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____13365 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____13364 uu____13365
                                           else ());
                                          (let uu____13367 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____13367 with
                                           | (vars,guards,env'1,binder_decls,uu____13383)
                                               ->
                                               let body1 =
                                                 let uu____13391 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____13391
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____13394 =
                                                 let uu____13399 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____13399
                                                 then
                                                   let uu____13405 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____13406 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____13405, uu____13406)
                                                 else
                                                   (let uu____13412 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____13412)) in
                                               (match uu____13394 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____13426 =
                                                        let uu____13430 =
                                                          let uu____13431 =
                                                            let uu____13437 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____13437) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____13431 in
                                                        let uu____13443 =
                                                          let uu____13445 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____13445 in
                                                        (uu____13430,
                                                          uu____13443,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____13426 in
                                                    let uu____13447 =
                                                      let uu____13449 =
                                                        let uu____13451 =
                                                          let uu____13453 =
                                                            let uu____13455 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____13455 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____13453 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____13451 in
                                                      FStar_List.append
                                                        decls1 uu____13449 in
                                                    (uu____13447, env1))))))
                           | uu____13458 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____13477 = varops.fresh "fuel" in
                             (uu____13477, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____13480 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____13530  ->
                                     fun uu____13531  ->
                                       match (uu____13530, uu____13531) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____13609 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____13609 in
                                           let gtok =
                                             let uu____13611 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____13611 in
                                           let env3 =
                                             let uu____13613 =
                                               let uu____13615 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_43) uu____13615 in
                                             push_free_var env2 flid gtok
                                               uu____13613 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____13480 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____13701
                                 t_norm uu____13703 =
                                 match (uu____13701, uu____13703) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____13730;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____13731;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____13748 =
                                       let uu____13752 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____13752 with
                                       | (tcenv',uu____13767,e_t) ->
                                           let uu____13771 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13778 ->
                                                 failwith "Impossible" in
                                           (match uu____13771 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13788 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13788.bindings);
                                                    depth =
                                                      (uu___150_13788.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13788.warn);
                                                    cache =
                                                      (uu___150_13788.cache);
                                                    nolabels =
                                                      (uu___150_13788.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13788.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13788.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13788.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____13748 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13798 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____13798
                                            then
                                              let uu____13799 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13800 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13801 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13799 uu____13800
                                                uu____13801
                                            else ());
                                           (let uu____13803 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13803 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13825 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____13825
                                                  then
                                                    let uu____13826 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13827 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13828 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13829 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13826 uu____13827
                                                      uu____13828 uu____13829
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13833 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____13833 with
                                                  | (vars,guards,env'1,binder_decls,uu____13851)
                                                      ->
                                                      let decl_g =
                                                        let uu____13859 =
                                                          let uu____13865 =
                                                            let uu____13867 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13867 in
                                                          (g, uu____13865,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13859 in
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
                                                        let uu____13882 =
                                                          let uu____13886 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13886) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13882 in
                                                      let gsapp =
                                                        let uu____13892 =
                                                          let uu____13896 =
                                                            let uu____13898 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13898 ::
                                                              vars_tm in
                                                          (g, uu____13896) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13892 in
                                                      let gmax =
                                                        let uu____13902 =
                                                          let uu____13906 =
                                                            let uu____13908 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13908 ::
                                                              vars_tm in
                                                          (g, uu____13906) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13902 in
                                                      let body1 =
                                                        let uu____13912 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13912
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____13914 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13914 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13925
                                                               =
                                                               let uu____13929
                                                                 =
                                                                 let uu____13930
                                                                   =
                                                                   let uu____13938
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
                                                                    uu____13938) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13930 in
                                                               let uu____13949
                                                                 =
                                                                 let uu____13951
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____13951 in
                                                               (uu____13929,
                                                                 uu____13949,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13925 in
                                                           let eqn_f =
                                                             let uu____13954
                                                               =
                                                               let uu____13958
                                                                 =
                                                                 let uu____13959
                                                                   =
                                                                   let uu____13965
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13965) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13959 in
                                                               (uu____13958,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13954 in
                                                           let eqn_g' =
                                                             let uu____13973
                                                               =
                                                               let uu____13977
                                                                 =
                                                                 let uu____13978
                                                                   =
                                                                   let uu____13984
                                                                    =
                                                                    let uu____13985
                                                                    =
                                                                    let uu____13988
                                                                    =
                                                                    let uu____13989
                                                                    =
                                                                    let uu____13993
                                                                    =
                                                                    let uu____13995
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____13995
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13993) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13989 in
                                                                    (gsapp,
                                                                    uu____13988) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13985 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13984) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13978 in
                                                               (uu____13977,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13973 in
                                                           let uu____14007 =
                                                             let uu____14012
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____14012
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____14029)
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
                                                                    let uu____14044
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____14044
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____14047
                                                                    =
                                                                    let uu____14051
                                                                    =
                                                                    let uu____14052
                                                                    =
                                                                    let uu____14058
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____14058) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14052 in
                                                                    (uu____14051,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14047 in
                                                                 let uu____14069
                                                                   =
                                                                   let uu____14073
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____14073
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____14081
                                                                    =
                                                                    let uu____14083
                                                                    =
                                                                    let uu____14084
                                                                    =
                                                                    let uu____14088
                                                                    =
                                                                    let uu____14089
                                                                    =
                                                                    let uu____14095
                                                                    =
                                                                    let uu____14096
                                                                    =
                                                                    let uu____14099
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____14099,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14096 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____14095) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14089 in
                                                                    (uu____14088,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14084 in
                                                                    [uu____14083] in
                                                                    (d3,
                                                                    uu____14081) in
                                                                 (match uu____14069
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____14007
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
                               let uu____14134 =
                                 let uu____14141 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____14189  ->
                                      fun uu____14190  ->
                                        match (uu____14189, uu____14190) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____14276 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____14276 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____14141 in
                               (match uu____14134 with
                                | (decls2,eqns,env01) ->
                                    let uu____14316 =
                                      let isDeclFun uu___117_14324 =
                                        match uu___117_14324 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____14325 -> true
                                        | uu____14331 -> false in
                                      let uu____14332 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____14332
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____14316 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____14362 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____14362
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
        let uu____14396 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____14396 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____14399 = encode_sigelt' env se in
      match uu____14399 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____14409 =
                  let uu____14410 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____14410 in
                [uu____14409]
            | uu____14411 ->
                let uu____14412 =
                  let uu____14414 =
                    let uu____14415 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____14415 in
                  uu____14414 :: g in
                let uu____14416 =
                  let uu____14418 =
                    let uu____14419 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____14419 in
                  [uu____14418] in
                FStar_List.append uu____14412 uu____14416 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____14429 =
          let uu____14430 = FStar_Syntax_Subst.compress t in
          uu____14430.FStar_Syntax_Syntax.n in
        match uu____14429 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____14434)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____14437 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____14440 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____14443 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____14445 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____14447 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____14455 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____14458 =
            let uu____14459 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____14459 Prims.op_Negation in
          if uu____14458
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____14479 ->
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
               let uu____14499 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____14499 with
               | (aname,atok,env2) ->
                   let uu____14509 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____14509 with
                    | (formals,uu____14519) ->
                        let uu____14526 =
                          let uu____14529 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____14529 env2 in
                        (match uu____14526 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____14537 =
                                 let uu____14538 =
                                   let uu____14544 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____14553  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____14544,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____14538 in
                               [uu____14537;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____14560 =
                               let aux uu____14589 uu____14590 =
                                 match (uu____14589, uu____14590) with
                                 | ((bv,uu____14617),(env3,acc_sorts,acc)) ->
                                     let uu____14638 = gen_term_var env3 bv in
                                     (match uu____14638 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____14560 with
                              | (uu____14676,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____14690 =
                                      let uu____14694 =
                                        let uu____14695 =
                                          let uu____14701 =
                                            let uu____14702 =
                                              let uu____14705 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____14705) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____14702 in
                                          ([[app]], xs_sorts, uu____14701) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14695 in
                                      (uu____14694,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14690 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____14717 =
                                      let uu____14721 =
                                        let uu____14722 =
                                          let uu____14728 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____14728) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14722 in
                                      (uu____14721,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14717 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____14738 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____14738 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14754,uu____14755)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____14756 = new_term_constant_and_tok_from_lid env lid in
          (match uu____14756 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14767,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____14772 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_14775  ->
                      match uu___118_14775 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____14776 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____14779 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14780 -> false)) in
            Prims.op_Negation uu____14772 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____14786 = encode_top_level_val env fv t quals in
             match uu____14786 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____14798 =
                   let uu____14800 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14800 in
                 (uu____14798, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____14806 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____14806 with
           | (uu____14811,f1) ->
               let uu____14813 = encode_formula f1 env in
               (match uu____14813 with
                | (f2,decls) ->
                    let g =
                      let uu____14822 =
                        let uu____14823 =
                          let uu____14827 =
                            let uu____14829 =
                              let uu____14830 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____14830 in
                            FStar_Pervasives_Native.Some uu____14829 in
                          let uu____14831 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____14827, uu____14831) in
                        FStar_SMTEncoding_Util.mkAssume uu____14823 in
                      [uu____14822] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14835) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____14842 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14857 =
                       let uu____14859 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14859.FStar_Syntax_Syntax.fv_name in
                     uu____14857.FStar_Syntax_Syntax.v in
                   let uu____14860 =
                     let uu____14861 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14861 in
                   if uu____14860
                   then
                     let val_decl =
                       let uu___151_14876 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14876.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14876.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_14876.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____14880 = encode_sigelt' env1 val_decl in
                     match uu____14880 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____14842 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14897,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14899;
                          FStar_Syntax_Syntax.lbtyp = uu____14900;
                          FStar_Syntax_Syntax.lbeff = uu____14901;
                          FStar_Syntax_Syntax.lbdef = uu____14902;_}::[]),uu____14903)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____14915 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14915 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____14934 =
                   let uu____14936 =
                     let uu____14937 =
                       let uu____14941 =
                         let uu____14942 =
                           let uu____14948 =
                             let uu____14949 =
                               let uu____14952 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14952) in
                             FStar_SMTEncoding_Util.mkEq uu____14949 in
                           ([[b2t_x]], [xx], uu____14948) in
                         FStar_SMTEncoding_Util.mkForall uu____14942 in
                       (uu____14941,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14937 in
                   [uu____14936] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____14934 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14969,uu____14970) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_14976  ->
                  match uu___119_14976 with
                  | FStar_Syntax_Syntax.Discriminator uu____14977 -> true
                  | uu____14978 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14980,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14988 =
                     let uu____14989 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14989.FStar_Ident.idText in
                   uu____14988 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_14992  ->
                     match uu___120_14992 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14993 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14996) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_15006  ->
                  match uu___121_15006 with
                  | FStar_Syntax_Syntax.Projector uu____15007 -> true
                  | uu____15010 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____15013 = try_lookup_free_var env l in
          (match uu____15013 with
           | FStar_Pervasives_Native.Some uu____15017 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_15020 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_15020.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_15020.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_15020.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____15026) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____15036) ->
          let uu____15041 = encode_sigelts env ses in
          (match uu____15041 with
           | (g,env1) ->
               let uu____15051 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_15065  ->
                         match uu___122_15065 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____15066;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____15067;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____15068;_}
                             -> false
                         | uu____15070 -> true)) in
               (match uu____15051 with
                | (g',inversions) ->
                    let uu____15079 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_15091  ->
                              match uu___123_15091 with
                              | FStar_SMTEncoding_Term.DeclFun uu____15092 ->
                                  true
                              | uu____15098 -> false)) in
                    (match uu____15079 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____15109,tps,k,uu____15112,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_15123  ->
                    match uu___124_15123 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____15124 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____15131 = c in
              match uu____15131 with
              | (name,args,uu____15135,uu____15136,uu____15137) ->
                  let uu____15140 =
                    let uu____15141 =
                      let uu____15147 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____15158  ->
                                match uu____15158 with
                                | (uu____15162,sort,uu____15164) -> sort)) in
                      (name, uu____15147, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____15141 in
                  [uu____15140]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____15182 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____15187 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____15187 FStar_Option.isNone)) in
            if uu____15182
            then []
            else
              (let uu____15204 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____15204 with
               | (xxsym,xx) ->
                   let uu____15210 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____15239  ->
                             fun l  ->
                               match uu____15239 with
                               | (out,decls) ->
                                   let uu____15251 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____15251 with
                                    | (uu____15257,data_t) ->
                                        let uu____15259 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____15259 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____15288 =
                                                 let uu____15289 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____15289.FStar_Syntax_Syntax.n in
                                               match uu____15288 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____15297,indices) ->
                                                   indices
                                               | uu____15313 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____15330  ->
                                                         match uu____15330
                                                         with
                                                         | (x,uu____15334) ->
                                                             let uu____15335
                                                               =
                                                               let uu____15336
                                                                 =
                                                                 let uu____15340
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____15340,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____15336 in
                                                             push_term_var
                                                               env1 x
                                                               uu____15335)
                                                    env) in
                                             let uu____15342 =
                                               encode_args indices env1 in
                                             (match uu____15342 with
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
                                                      let uu____15366 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____15377
                                                                 =
                                                                 let uu____15380
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____15380,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____15377)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____15366
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____15382 =
                                                      let uu____15383 =
                                                        let uu____15386 =
                                                          let uu____15387 =
                                                            let uu____15390 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____15390,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____15387 in
                                                        (out, uu____15386) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____15383 in
                                                    (uu____15382,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____15210 with
                    | (data_ax,decls) ->
                        let uu____15398 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____15398 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____15412 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____15412 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____15415 =
                                 let uu____15419 =
                                   let uu____15420 =
                                     let uu____15426 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____15434 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____15426,
                                       uu____15434) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____15420 in
                                 let uu____15442 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____15419,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____15442) in
                               FStar_SMTEncoding_Util.mkAssume uu____15415 in
                             let pattern_guarded_inversion =
                               let uu____15446 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____15446
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____15457 =
                                   let uu____15458 =
                                     let uu____15462 =
                                       let uu____15463 =
                                         let uu____15469 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____15477 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____15469, uu____15477) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____15463 in
                                     let uu____15485 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____15462,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____15485) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____15458 in
                                 [uu____15457]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____15488 =
            let uu____15496 =
              let uu____15497 = FStar_Syntax_Subst.compress k in
              uu____15497.FStar_Syntax_Syntax.n in
            match uu____15496 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____15526 -> (tps, k) in
          (match uu____15488 with
           | (formals,res) ->
               let uu____15541 = FStar_Syntax_Subst.open_term formals res in
               (match uu____15541 with
                | (formals1,res1) ->
                    let uu____15548 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____15548 with
                     | (vars,guards,env',binder_decls,uu____15563) ->
                         let uu____15570 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____15570 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____15583 =
                                  let uu____15587 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____15587) in
                                FStar_SMTEncoding_Util.mkApp uu____15583 in
                              let uu____15592 =
                                let tname_decl =
                                  let uu____15598 =
                                    let uu____15599 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____15617  ->
                                              match uu____15617 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____15625 = varops.next_id () in
                                    (tname, uu____15599,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____15625, false) in
                                  constructor_or_logic_type_decl uu____15598 in
                                let uu____15630 =
                                  match vars with
                                  | [] ->
                                      let uu____15637 =
                                        let uu____15638 =
                                          let uu____15640 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____15640 in
                                        push_free_var env1 t tname
                                          uu____15638 in
                                      ([], uu____15637)
                                  | uu____15644 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____15650 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____15650 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____15659 =
                                          let uu____15663 =
                                            let uu____15664 =
                                              let uu____15672 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____15672) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____15664 in
                                          (uu____15663,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____15659 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____15630 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____15592 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____15695 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____15695 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____15712 =
                                               let uu____15713 =
                                                 let uu____15717 =
                                                   let uu____15718 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____15718 in
                                                 (uu____15717,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15713 in
                                             [uu____15712]
                                           else [] in
                                         let uu____15721 =
                                           let uu____15723 =
                                             let uu____15725 =
                                               let uu____15726 =
                                                 let uu____15730 =
                                                   let uu____15731 =
                                                     let uu____15737 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____15737) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____15731 in
                                                 (uu____15730,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15726 in
                                             [uu____15725] in
                                           FStar_List.append karr uu____15723 in
                                         FStar_List.append decls1 uu____15721 in
                                   let aux =
                                     let uu____15746 =
                                       let uu____15748 =
                                         inversion_axioms tapp vars in
                                       let uu____15750 =
                                         let uu____15752 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____15752] in
                                       FStar_List.append uu____15748
                                         uu____15750 in
                                     FStar_List.append kindingAx uu____15746 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15757,uu____15758,uu____15759,uu____15760,uu____15761)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15766,t,uu____15768,n_tps,uu____15770) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____15775 = new_term_constant_and_tok_from_lid env d in
          (match uu____15775 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____15786 = FStar_Syntax_Util.arrow_formals t in
               (match uu____15786 with
                | (formals,t_res) ->
                    let uu____15808 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____15808 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____15817 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____15817 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____15859 =
                                            mk_term_projector_name d x in
                                          (uu____15859,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15861 =
                                  let uu____15871 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15871, true) in
                                FStar_All.pipe_right uu____15861
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
                              let uu____15893 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____15893 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15901::uu____15902 ->
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
                                         let uu____15927 =
                                           let uu____15933 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15933) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15927
                                     | uu____15946 -> tok_typing in
                                   let uu____15951 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____15951 with
                                    | (vars',guards',env'',decls_formals,uu____15966)
                                        ->
                                        let uu____15973 =
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
                                        (match uu____15973 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15992 ->
                                                   let uu____15996 =
                                                     let uu____15997 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15997 in
                                                   [uu____15996] in
                                             let encode_elim uu____16004 =
                                               let uu____16005 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____16005 with
                                               | (head1,args) ->
                                                   let uu____16034 =
                                                     let uu____16035 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____16035.FStar_Syntax_Syntax.n in
                                                   (match uu____16034 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____16042;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____16043;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____16044;_},uu____16045)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____16051 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____16051
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
                                                                 | uu____16080
                                                                    ->
                                                                    let uu____16081
                                                                    =
                                                                    let uu____16082
                                                                    =
                                                                    let uu____16085
                                                                    =
                                                                    let uu____16086
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16086 in
                                                                    (uu____16085,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____16082 in
                                                                    raise
                                                                    uu____16081 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16097
                                                                    =
                                                                    let uu____16098
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16098 in
                                                                    if
                                                                    uu____16097
                                                                    then
                                                                    let uu____16105
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____16105]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____16107
                                                               =
                                                               let uu____16114
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____16147
                                                                     ->
                                                                    fun
                                                                    uu____16148
                                                                     ->
                                                                    match 
                                                                    (uu____16147,
                                                                    uu____16148)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16199
                                                                    =
                                                                    let uu____16203
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____16203 in
                                                                    (match uu____16199
                                                                    with
                                                                    | 
                                                                    (uu____16210,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16216
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____16216
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16218
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____16218
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
                                                                 uu____16114 in
                                                             (match uu____16107
                                                              with
                                                              | (uu____16226,arg_vars,elim_eqns_or_guards,uu____16229)
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
                                                                    let uu____16248
                                                                    =
                                                                    let uu____16252
                                                                    =
                                                                    let uu____16253
                                                                    =
                                                                    let uu____16259
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16265
                                                                    =
                                                                    let uu____16266
                                                                    =
                                                                    let uu____16269
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____16269) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16266 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16259,
                                                                    uu____16265) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16253 in
                                                                    (uu____16252,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16248 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____16282
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____16282,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____16284
                                                                    =
                                                                    let uu____16288
                                                                    =
                                                                    let uu____16289
                                                                    =
                                                                    let uu____16295
                                                                    =
                                                                    let uu____16298
                                                                    =
                                                                    let uu____16300
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____16300] in
                                                                    [uu____16298] in
                                                                    let uu____16303
                                                                    =
                                                                    let uu____16304
                                                                    =
                                                                    let uu____16307
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____16308
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____16307,
                                                                    uu____16308) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16304 in
                                                                    (uu____16295,
                                                                    [x],
                                                                    uu____16303) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16289 in
                                                                    let uu____16318
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____16288,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16318) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16284
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16323
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
                                                                    (let uu____16340
                                                                    =
                                                                    let uu____16341
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____16341
                                                                    dapp1 in
                                                                    [uu____16340]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____16323
                                                                    FStar_List.flatten in
                                                                    let uu____16345
                                                                    =
                                                                    let uu____16349
                                                                    =
                                                                    let uu____16350
                                                                    =
                                                                    let uu____16356
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16362
                                                                    =
                                                                    let uu____16363
                                                                    =
                                                                    let uu____16366
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16366) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16363 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16356,
                                                                    uu____16362) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16350 in
                                                                    (uu____16349,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16345) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____16378 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____16378
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
                                                                 | uu____16407
                                                                    ->
                                                                    let uu____16408
                                                                    =
                                                                    let uu____16409
                                                                    =
                                                                    let uu____16412
                                                                    =
                                                                    let uu____16413
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____16413 in
                                                                    (uu____16412,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____16409 in
                                                                    raise
                                                                    uu____16408 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____16424
                                                                    =
                                                                    let uu____16425
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____16425 in
                                                                    if
                                                                    uu____16424
                                                                    then
                                                                    let uu____16432
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____16432]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____16434
                                                               =
                                                               let uu____16441
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____16474
                                                                     ->
                                                                    fun
                                                                    uu____16475
                                                                     ->
                                                                    match 
                                                                    (uu____16474,
                                                                    uu____16475)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____16526
                                                                    =
                                                                    let uu____16530
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____16530 in
                                                                    (match uu____16526
                                                                    with
                                                                    | 
                                                                    (uu____16537,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____16543
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____16543
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____16545
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____16545
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
                                                                 uu____16441 in
                                                             (match uu____16434
                                                              with
                                                              | (uu____16553,arg_vars,elim_eqns_or_guards,uu____16556)
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
                                                                    let uu____16575
                                                                    =
                                                                    let uu____16579
                                                                    =
                                                                    let uu____16580
                                                                    =
                                                                    let uu____16586
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16592
                                                                    =
                                                                    let uu____16593
                                                                    =
                                                                    let uu____16596
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____16596) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16593 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16586,
                                                                    uu____16592) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16580 in
                                                                    (uu____16579,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16575 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____16609
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____16609,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____16611
                                                                    =
                                                                    let uu____16615
                                                                    =
                                                                    let uu____16616
                                                                    =
                                                                    let uu____16622
                                                                    =
                                                                    let uu____16625
                                                                    =
                                                                    let uu____16627
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____16627] in
                                                                    [uu____16625] in
                                                                    let uu____16630
                                                                    =
                                                                    let uu____16631
                                                                    =
                                                                    let uu____16634
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____16635
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____16634,
                                                                    uu____16635) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16631 in
                                                                    (uu____16622,
                                                                    [x],
                                                                    uu____16630) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16616 in
                                                                    let uu____16645
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____16615,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____16645) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16611
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____16650
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
                                                                    (let uu____16667
                                                                    =
                                                                    let uu____16668
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____16668
                                                                    dapp1 in
                                                                    [uu____16667]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____16650
                                                                    FStar_List.flatten in
                                                                    let uu____16672
                                                                    =
                                                                    let uu____16676
                                                                    =
                                                                    let uu____16677
                                                                    =
                                                                    let uu____16683
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16689
                                                                    =
                                                                    let uu____16690
                                                                    =
                                                                    let uu____16693
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16693) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16690 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16683,
                                                                    uu____16689) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16677 in
                                                                    (uu____16676,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16672) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____16703 ->
                                                        ((let uu____16705 =
                                                            let uu____16706 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____16707 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____16706
                                                              uu____16707 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____16705);
                                                         ([], []))) in
                                             let uu____16710 = encode_elim () in
                                             (match uu____16710 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____16722 =
                                                      let uu____16724 =
                                                        let uu____16726 =
                                                          let uu____16728 =
                                                            let uu____16730 =
                                                              let uu____16731
                                                                =
                                                                let uu____16737
                                                                  =
                                                                  let uu____16739
                                                                    =
                                                                    let uu____16740
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16740 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____16739 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____16737) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____16731 in
                                                            [uu____16730] in
                                                          let uu____16743 =
                                                            let uu____16745 =
                                                              let uu____16747
                                                                =
                                                                let uu____16749
                                                                  =
                                                                  let uu____16751
                                                                    =
                                                                    let uu____16753
                                                                    =
                                                                    let uu____16755
                                                                    =
                                                                    let uu____16756
                                                                    =
                                                                    let uu____16760
                                                                    =
                                                                    let uu____16761
                                                                    =
                                                                    let uu____16767
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16767) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16761 in
                                                                    (uu____16760,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16756 in
                                                                    let uu____16774
                                                                    =
                                                                    let uu____16776
                                                                    =
                                                                    let uu____16777
                                                                    =
                                                                    let uu____16781
                                                                    =
                                                                    let uu____16782
                                                                    =
                                                                    let uu____16788
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____16794
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16788,
                                                                    uu____16794) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16782 in
                                                                    (uu____16781,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16777 in
                                                                    [uu____16776] in
                                                                    uu____16755
                                                                    ::
                                                                    uu____16774 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____16753 in
                                                                  FStar_List.append
                                                                    uu____16751
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____16749 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____16747 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____16745 in
                                                          FStar_List.append
                                                            uu____16728
                                                            uu____16743 in
                                                        FStar_List.append
                                                          decls3 uu____16726 in
                                                      FStar_List.append
                                                        decls2 uu____16724 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____16722 in
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
           (fun uu____16822  ->
              fun se  ->
                match uu____16822 with
                | (g,env1) ->
                    let uu____16834 = encode_sigelt env1 se in
                    (match uu____16834 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16872 =
        match uu____16872 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____16890 ->
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
                 ((let uu____16895 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____16895
                   then
                     let uu____16896 = FStar_Syntax_Print.bv_to_string x in
                     let uu____16897 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____16898 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16896 uu____16897 uu____16898
                   else ());
                  (let uu____16900 = encode_term t1 env1 in
                   match uu____16900 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____16910 =
                         let uu____16914 =
                           let uu____16915 =
                             let uu____16916 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____16916
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____16915 in
                         new_term_constant_from_string env1 x uu____16914 in
                       (match uu____16910 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____16927 = FStar_Options.log_queries () in
                              if uu____16927
                              then
                                let uu____16929 =
                                  let uu____16930 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____16931 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____16932 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16930 uu____16931 uu____16932 in
                                FStar_Pervasives_Native.Some uu____16929
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____16943,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____16952 = encode_free_var env1 fv t t_norm [] in
                 (match uu____16952 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____16965,se,uu____16967) ->
                 let uu____16970 = encode_sigelt env1 se in
                 (match uu____16970 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16980,se) ->
                 let uu____16984 = encode_sigelt env1 se in
                 (match uu____16984 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16994 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16994 with | (uu____17006,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____17058  ->
            match uu____17058 with
            | (l,uu____17065,uu____17066) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____17093  ->
            match uu____17093 with
            | (l,uu____17101,uu____17102) ->
                let uu____17107 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                    (FStar_Pervasives_Native.fst l) in
                let uu____17108 =
                  let uu____17110 =
                    let uu____17111 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____17111 in
                  [uu____17110] in
                uu____17107 :: uu____17108)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____17123 =
      let uu____17125 =
        let uu____17126 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____17128 =
          let uu____17129 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____17129 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____17126;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____17128
        } in
      [uu____17125] in
    FStar_ST.write last_env uu____17123
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____17141 = FStar_ST.read last_env in
      match uu____17141 with
      | [] -> failwith "No env; call init first!"
      | e::uu____17147 ->
          let uu___153_17149 = e in
          let uu____17150 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_17149.bindings);
            depth = (uu___153_17149.depth);
            tcenv;
            warn = (uu___153_17149.warn);
            cache = (uu___153_17149.cache);
            nolabels = (uu___153_17149.nolabels);
            use_zfuel_name = (uu___153_17149.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_17149.encode_non_total_function_typ);
            current_module_name = uu____17150
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____17155 = FStar_ST.read last_env in
    match uu____17155 with
    | [] -> failwith "Empty env stack"
    | uu____17160::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____17169  ->
    let uu____17170 = FStar_ST.read last_env in
    match uu____17170 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_17181 = hd1 in
          {
            bindings = (uu___154_17181.bindings);
            depth = (uu___154_17181.depth);
            tcenv = (uu___154_17181.tcenv);
            warn = (uu___154_17181.warn);
            cache = refs;
            nolabels = (uu___154_17181.nolabels);
            use_zfuel_name = (uu___154_17181.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_17181.encode_non_total_function_typ);
            current_module_name = (uu___154_17181.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____17188  ->
    let uu____17189 = FStar_ST.read last_env in
    match uu____17189 with
    | [] -> failwith "Popping an empty stack"
    | uu____17194::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____17203  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____17207  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____17211  ->
    let uu____17212 = FStar_ST.read last_env in
    match uu____17212 with
    | hd1::uu____17218::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____17224 -> failwith "Impossible"
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
        | (uu____17283::uu____17284,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_17290 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_17290.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_17290.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_17290.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____17291 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____17304 =
        let uu____17306 =
          let uu____17307 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____17307 in
        let uu____17308 = open_fact_db_tags env in uu____17306 :: uu____17308 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____17304
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
      let uu____17325 = encode_sigelt env se in
      match uu____17325 with
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
        let uu____17352 = FStar_Options.log_queries () in
        if uu____17352
        then
          let uu____17354 =
            let uu____17355 =
              let uu____17356 =
                let uu____17357 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____17357 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____17356 in
            FStar_SMTEncoding_Term.Caption uu____17355 in
          uu____17354 :: decls
        else decls in
      let env =
        let uu____17364 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17364 tcenv in
      let uu____17365 = encode_top_level_facts env se in
      match uu____17365 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____17374 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____17374))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____17387 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____17387
       then
         let uu____17388 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____17388
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____17418  ->
                 fun se  ->
                   match uu____17418 with
                   | (g,env2) ->
                       let uu____17430 = encode_top_level_facts env2 se in
                       (match uu____17430 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____17443 =
         encode_signature
           (let uu___156_17449 = env in
            {
              bindings = (uu___156_17449.bindings);
              depth = (uu___156_17449.depth);
              tcenv = (uu___156_17449.tcenv);
              warn = false;
              cache = (uu___156_17449.cache);
              nolabels = (uu___156_17449.nolabels);
              use_zfuel_name = (uu___156_17449.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_17449.encode_non_total_function_typ);
              current_module_name = (uu___156_17449.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____17443 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____17461 = FStar_Options.log_queries () in
             if uu____17461
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_17468 = env1 in
               {
                 bindings = (uu___157_17468.bindings);
                 depth = (uu___157_17468.depth);
                 tcenv = (uu___157_17468.tcenv);
                 warn = true;
                 cache = (uu___157_17468.cache);
                 nolabels = (uu___157_17468.nolabels);
                 use_zfuel_name = (uu___157_17468.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_17468.encode_non_total_function_typ);
                 current_module_name = (uu___157_17468.current_module_name)
               });
            (let uu____17470 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____17470
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
        (let uu____17508 =
           let uu____17509 = FStar_TypeChecker_Env.current_module tcenv in
           uu____17509.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____17508);
        (let env =
           let uu____17511 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____17511 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____17520 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____17541 = aux rest in
                 (match uu____17541 with
                  | (out,rest1) ->
                      let t =
                        let uu____17559 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____17559 with
                        | FStar_Pervasives_Native.Some uu____17563 ->
                            let uu____17564 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____17564
                              x.FStar_Syntax_Syntax.sort
                        | uu____17565 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____17568 =
                        let uu____17570 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_17573 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_17573.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_17573.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____17570 :: out in
                      (uu____17568, rest1))
             | uu____17576 -> ([], bindings1) in
           let uu____17580 = aux bindings in
           match uu____17580 with
           | (closing,bindings1) ->
               let uu____17594 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____17594, bindings1) in
         match uu____17520 with
         | (q1,bindings1) ->
             let uu____17607 =
               let uu____17610 =
                 FStar_List.filter
                   (fun uu___125_17614  ->
                      match uu___125_17614 with
                      | FStar_TypeChecker_Env.Binding_sig uu____17615 ->
                          false
                      | uu____17619 -> true) bindings1 in
               encode_env_bindings env uu____17610 in
             (match uu____17607 with
              | (env_decls,env1) ->
                  ((let uu____17630 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____17630
                    then
                      let uu____17631 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____17631
                    else ());
                   (let uu____17633 = encode_formula q1 env1 in
                    match uu____17633 with
                    | (phi,qdecls) ->
                        let uu____17645 =
                          let uu____17648 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____17648 phi in
                        (match uu____17645 with
                         | (labels,phi1) ->
                             let uu____17658 = encode_labels labels in
                             (match uu____17658 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____17679 =
                                      let uu____17683 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____17684 =
                                        varops.mk_unique "@query" in
                                      (uu____17683,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17684) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17679 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____17699 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17699 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____17701 = encode_formula q env in
       match uu____17701 with
       | (f,uu____17705) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____17707) -> true
             | uu____17710 -> false)))