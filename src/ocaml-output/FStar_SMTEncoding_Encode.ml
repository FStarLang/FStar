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
        (let uu____3043 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3043
         then
           let uu____3044 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3044
         else ());
        (let uu____3046 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3095  ->
                   fun b  ->
                     match uu____3095 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3138 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____3147 = gen_term_var env1 x in
                           match uu____3147 with
                           | (xxsym,xx,env') ->
                               let uu____3161 =
                                 let uu____3164 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3164 env1 xx in
                               (match uu____3161 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____3138 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____3046 with
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
          let uu____3252 = encode_term t env in
          match uu____3252 with
          | (t1,decls) ->
              let uu____3259 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3259, decls)
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
          let uu____3267 = encode_term t env in
          match uu____3267 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____3276 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3276, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____3278 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3278, decls))
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
        let uu____3284 = encode_args args_e env in
        match uu____3284 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3296 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3303 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3303 in
            let binary arg_tms1 =
              let uu____3312 =
                let uu____3313 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3313 in
              let uu____3314 =
                let uu____3315 =
                  let uu____3316 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3316 in
                FStar_SMTEncoding_Term.unboxInt uu____3315 in
              (uu____3312, uu____3314) in
            let mk_default uu____3321 =
              let uu____3322 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3322 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3363 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3363
              then
                let uu____3364 = let uu____3365 = mk_args ts in op uu____3365 in
                FStar_All.pipe_right uu____3364 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3388 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3388
              then
                let uu____3389 = binary ts in
                match uu____3389 with
                | (t1,t2) ->
                    let uu____3394 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3394
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3397 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3397
                 then
                   let uu____3398 = op (binary ts) in
                   FStar_All.pipe_right uu____3398
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
            let uu____3488 =
              let uu____3494 =
                FStar_List.tryFind
                  (fun uu____3509  ->
                     match uu____3509 with
                     | (l,uu____3516) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3494 FStar_Util.must in
            (match uu____3488 with
             | (uu____3541,op) ->
                 let uu____3549 = op arg_tms in (uu____3549, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____3556 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3556
       then
         let uu____3557 = FStar_Syntax_Print.tag_of_term t in
         let uu____3558 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3559 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3557 uu____3558
           uu____3559
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3563 ->
           let uu____3578 =
             let uu____3579 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3580 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3581 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3582 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3579
               uu____3580 uu____3581 uu____3582 in
           failwith uu____3578
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3585 =
             let uu____3586 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3587 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3588 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3589 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3586
               uu____3587 uu____3588 uu____3589 in
           failwith uu____3585
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3593 =
             let uu____3594 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3594 in
           failwith uu____3593
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3599) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3629) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3638 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3638, [])
       | FStar_Syntax_Syntax.Tm_type uu____3640 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3643) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3649 = encode_const c in (uu____3649, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3664 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3664 with
            | (binders1,res) ->
                let uu____3671 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3671
                then
                  let uu____3674 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____3674 with
                   | (vars,guards,env',decls,uu____3689) ->
                       let fsym =
                         let uu____3699 = varops.fresh "f" in
                         (uu____3699, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3702 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3708 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3708.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3708.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3708.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3708.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3708.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3708.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3708.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3708.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3708.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3708.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3708.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3708.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3708.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3708.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3708.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3708.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3708.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3708.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3708.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3708.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3708.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3708.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3708.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_3708.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_3708.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_3708.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____3702 with
                        | (pre_opt,res_t) ->
                            let uu____3715 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____3715 with
                             | (res_pred,decls') ->
                                 let uu____3722 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____3729 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3729, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____3732 =
                                         encode_formula pre env' in
                                       (match uu____3732 with
                                        | (guard,decls0) ->
                                            let uu____3740 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3740, decls0)) in
                                 (match uu____3722 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3748 =
                                          let uu____3754 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3754) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3748 in
                                      let cvars =
                                        let uu____3764 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3764
                                          (FStar_List.filter
                                             (fun uu____3773  ->
                                                match uu____3773 with
                                                | (x,uu____3777) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3788 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3788 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____3793 =
                                             let uu____3794 =
                                               let uu____3798 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3798) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3794 in
                                           (uu____3793,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____3809 =
                                               let uu____3810 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3810 in
                                             varops.mk_unique uu____3809 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____3817 =
                                               FStar_Options.log_queries () in
                                             if uu____3817
                                             then
                                               let uu____3819 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____3819
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3825 =
                                               let uu____3829 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3829) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3825 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3837 =
                                               let uu____3841 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3841,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3837 in
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
                                             let uu____3854 =
                                               let uu____3858 =
                                                 let uu____3859 =
                                                   let uu____3865 =
                                                     let uu____3866 =
                                                       let uu____3869 =
                                                         let uu____3870 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3870 in
                                                       (f_has_t, uu____3869) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3866 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3865) in
                                                 mkForall_fuel uu____3859 in
                                               (uu____3858,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3854 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3883 =
                                               let uu____3887 =
                                                 let uu____3888 =
                                                   let uu____3894 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3894) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3888 in
                                               (uu____3887,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3883 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3908 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3908);
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
                     let uu____3919 =
                       let uu____3923 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3923,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3919 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3932 =
                       let uu____3936 =
                         let uu____3937 =
                           let uu____3943 =
                             let uu____3944 =
                               let uu____3947 =
                                 let uu____3948 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3948 in
                               (f_has_t, uu____3947) in
                             FStar_SMTEncoding_Util.mkImp uu____3944 in
                           ([[f_has_t]], [fsym], uu____3943) in
                         mkForall_fuel uu____3937 in
                       (uu____3936, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3932 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3962 ->
           let uu____3967 =
             let uu____3970 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3970 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3975;
                 FStar_Syntax_Syntax.pos = uu____3976;
                 FStar_Syntax_Syntax.vars = uu____3977;_} ->
                 let uu____3984 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____3984 with
                  | (b,f1) ->
                      let uu____3998 =
                        let uu____3999 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____3999 in
                      (uu____3998, f1))
             | uu____4004 -> failwith "impossible" in
           (match uu____3967 with
            | (x,f) ->
                let uu____4011 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4011 with
                 | (base_t,decls) ->
                     let uu____4018 = gen_term_var env x in
                     (match uu____4018 with
                      | (x1,xtm,env') ->
                          let uu____4027 = encode_formula f env' in
                          (match uu____4027 with
                           | (refinement,decls') ->
                               let uu____4034 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4034 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4045 =
                                        let uu____4047 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4051 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4047
                                          uu____4051 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4045 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4070  ->
                                              match uu____4070 with
                                              | (y,uu____4074) ->
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
                                    let uu____4093 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4093 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____4098 =
                                           let uu____4099 =
                                             let uu____4103 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4103) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4099 in
                                         (uu____4098,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____4115 =
                                             let uu____4116 =
                                               let uu____4117 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4117 in
                                             Prims.strcat module_name
                                               uu____4116 in
                                           varops.mk_unique uu____4115 in
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
                                           let uu____4126 =
                                             let uu____4130 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4130) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4126 in
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
                                           let uu____4141 =
                                             let uu____4145 =
                                               let uu____4146 =
                                                 let uu____4152 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4152) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4146 in
                                             (uu____4145,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4141 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4167 =
                                             let uu____4171 =
                                               let uu____4172 =
                                                 let uu____4178 =
                                                   let uu____4179 =
                                                     let uu____4182 =
                                                       let uu____4183 =
                                                         let uu____4189 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4189) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4183 in
                                                     (uu____4182, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4179 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4178) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4172 in
                                             (uu____4171,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4167 in
                                         let t_kinding =
                                           let uu____4209 =
                                             let uu____4213 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4213,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4209 in
                                         let t_interp =
                                           let uu____4223 =
                                             let uu____4227 =
                                               let uu____4228 =
                                                 let uu____4234 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4234) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4228 in
                                             let uu____4246 =
                                               let uu____4248 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____4248 in
                                             (uu____4227, uu____4246,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4223 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4253 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4253);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4274 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4274 in
           let uu____4275 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____4275 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4283 =
                    let uu____4287 =
                      let uu____4288 =
                        let uu____4289 =
                          let uu____4290 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4290 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4289 in
                      varops.mk_unique uu____4288 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____4287) in
                  FStar_SMTEncoding_Util.mkAssume uu____4283 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4293 ->
           let uu____4303 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4303 with
            | (head1,args_e) ->
                let uu____4331 =
                  let uu____4339 =
                    let uu____4340 = FStar_Syntax_Subst.compress head1 in
                    uu____4340.FStar_Syntax_Syntax.n in
                  (uu____4339, args_e) in
                (match uu____4331 with
                 | uu____4350 when head_redex env head1 ->
                     let uu____4358 = whnf env t in
                     encode_term uu____4358 env
                 | uu____4359 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____4372;
                       FStar_Syntax_Syntax.pos = uu____4373;
                       FStar_Syntax_Syntax.vars = uu____4374;_},uu____4375),uu____4376::
                    (v1,uu____4378)::(v2,uu____4380)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4418 = encode_term v1 env in
                     (match uu____4418 with
                      | (v11,decls1) ->
                          let uu____4425 = encode_term v2 env in
                          (match uu____4425 with
                           | (v21,decls2) ->
                               let uu____4432 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4432,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4435::(v1,uu____4437)::(v2,uu____4439)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____4473 = encode_term v1 env in
                     (match uu____4473 with
                      | (v11,decls1) ->
                          let uu____4480 = encode_term v2 env in
                          (match uu____4480 with
                           | (v21,decls2) ->
                               let uu____4487 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4487,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4489) ->
                     let e0 =
                       let uu____4501 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____4501 in
                     ((let uu____4507 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____4507
                       then
                         let uu____4508 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4508
                       else ());
                      (let e =
                         let uu____4513 =
                           let uu____4514 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____4515 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4514
                             uu____4515 in
                         uu____4513 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4524),(arg,uu____4526)::[]) -> encode_term arg env
                 | uu____4544 ->
                     let uu____4552 = encode_args args_e env in
                     (match uu____4552 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4585 = encode_term head1 env in
                            match uu____4585 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____4624 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4624 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4674  ->
                                                 fun uu____4675  ->
                                                   match (uu____4674,
                                                           uu____4675)
                                                   with
                                                   | ((bv,uu____4689),
                                                      (a,uu____4691)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4705 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4705
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4710 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____4710 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4720 =
                                                   let uu____4724 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4729 =
                                                     let uu____4730 =
                                                       let uu____4731 =
                                                         let uu____4732 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4732 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4731 in
                                                     varops.mk_unique
                                                       uu____4730 in
                                                   (uu____4724,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____4729) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4720 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4743 = lookup_free_var_sym env fv in
                            match uu____4743 with
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
                                   FStar_Syntax_Syntax.tk = uu____4764;
                                   FStar_Syntax_Syntax.pos = uu____4765;
                                   FStar_Syntax_Syntax.vars = uu____4766;_},uu____4767)
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
                                   FStar_Syntax_Syntax.tk = uu____4778;
                                   FStar_Syntax_Syntax.pos = uu____4779;
                                   FStar_Syntax_Syntax.vars = uu____4780;_},uu____4781)
                                ->
                                let uu____4786 =
                                  let uu____4787 =
                                    let uu____4790 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4790
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4787
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4786
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4806 =
                                  let uu____4807 =
                                    let uu____4810 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4810
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4807
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4806
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4825,(FStar_Util.Inl t1,uu____4827),uu____4828)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4866,(FStar_Util.Inr c,uu____4868),uu____4869)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____4907 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____4927 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4927 in
                               let uu____4928 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4928 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4938;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4939;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4940;_},uu____4941)
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
                                     | uu____4967 ->
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
           let uu____5007 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____5007 with
            | (bs1,body1,opening) ->
                let fallback uu____5022 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____5027 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____5027, [decl]) in
                let is_impure rc =
                  let uu____5033 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____5033 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____5042 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5042
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____5055 = FStar_Syntax_Syntax.mk_Total res_typ in
                    FStar_Pervasives_Native.Some uu____5055
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____5058 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       FStar_Pervasives_Native.Some uu____5058)
                    else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____5063 =
                         let uu____5064 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5064 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5063);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____5066 =
                       (is_impure rc) &&
                         (let uu____5068 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____5068) in
                     if uu____5066
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5073 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____5073 with
                        | (vars,guards,envbody,decls,uu____5088) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____5096 = encode_term body2 envbody in
                            (match uu____5096 with
                             | (body3,decls') ->
                                 let uu____5103 =
                                   let uu____5108 = codomain_eff rc in
                                   match uu____5108 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____5120 = encode_term tfun env in
                                       (match uu____5120 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1)) in
                                 (match uu____5103 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5139 =
                                          let uu____5145 =
                                            let uu____5146 =
                                              let uu____5149 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____5149, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5146 in
                                          ([], vars, uu____5145) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5139 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____5157 =
                                              let uu____5159 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____5159
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5157 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____5170 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____5170 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____5175 =
                                             let uu____5176 =
                                               let uu____5180 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5180) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5176 in
                                           (uu____5175,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____5186 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____5186 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____5193 =
                                                    let uu____5194 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____5194 = cache_size in
                                                  if uu____5193
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
                                                    let uu____5205 =
                                                      let uu____5206 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5206 in
                                                    varops.mk_unique
                                                      uu____5205 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None) in
                                                let f =
                                                  let uu____5211 =
                                                    let uu____5215 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____5215) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5211 in
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
                                                      let uu____5227 =
                                                        let uu____5228 =
                                                          let uu____5232 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____5232,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5228 in
                                                      [uu____5227] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____5240 =
                                                    let uu____5244 =
                                                      let uu____5245 =
                                                        let uu____5251 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5251) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5245 in
                                                    (uu____5244,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5240 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____5261 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5261);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5263,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5264;
                          FStar_Syntax_Syntax.lbunivs = uu____5265;
                          FStar_Syntax_Syntax.lbtyp = uu____5266;
                          FStar_Syntax_Syntax.lbeff = uu____5267;
                          FStar_Syntax_Syntax.lbdef = uu____5268;_}::uu____5269),uu____5270)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5288;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5290;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5306 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____5319 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5319, [decl_e])))
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
              let uu____5359 = encode_term e1 env in
              match uu____5359 with
              | (ee1,decls1) ->
                  let uu____5366 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____5366 with
                   | (xs,e21) ->
                       let uu____5380 = FStar_List.hd xs in
                       (match uu____5380 with
                        | (x1,uu____5388) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5390 = encode_body e21 env' in
                            (match uu____5390 with
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
            let uu____5412 =
              let uu____5416 =
                let uu____5417 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5417 in
              gen_term_var env uu____5416 in
            match uu____5412 with
            | (scrsym,scr',env1) ->
                let uu____5427 = encode_term e env1 in
                (match uu____5427 with
                 | (scr,decls) ->
                     let uu____5434 =
                       let encode_branch b uu____5450 =
                         match uu____5450 with
                         | (else_case,decls1) ->
                             let uu____5461 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5461 with
                              | (p,w,br) ->
                                  let uu____5480 = encode_pat env1 p in
                                  (match uu____5480 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____5504  ->
                                                   match uu____5504 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____5509 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____5524 =
                                               encode_term w1 env2 in
                                             (match uu____5524 with
                                              | (w2,decls2) ->
                                                  let uu____5532 =
                                                    let uu____5533 =
                                                      let uu____5536 =
                                                        let uu____5537 =
                                                          let uu____5540 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5540) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5537 in
                                                      (guard, uu____5536) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5533 in
                                                  (uu____5532, decls2)) in
                                       (match uu____5509 with
                                        | (guard1,decls2) ->
                                            let uu____5548 =
                                              encode_br br env2 in
                                            (match uu____5548 with
                                             | (br1,decls3) ->
                                                 let uu____5556 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5556,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____5434 with
                      | (match_tm,decls1) ->
                          let uu____5567 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5567, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____5589 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5589
       then
         let uu____5590 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5590
       else ());
      (let uu____5592 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5592 with
       | (vars,pat_term) ->
           let uu____5602 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5633  ->
                     fun v1  ->
                       match uu____5633 with
                       | (env1,vars1) ->
                           let uu____5661 = gen_term_var env1 v1 in
                           (match uu____5661 with
                            | (xx,uu____5673,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5602 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5718 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5719 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5720 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5726 =
                        let uu____5729 = encode_const c in
                        (scrutinee, uu____5729) in
                      FStar_SMTEncoding_Util.mkEq uu____5726
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5742 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5742 with
                        | (uu____5746,uu____5747::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5749 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5770  ->
                                  match uu____5770 with
                                  | (arg,uu____5775) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5779 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5779)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5797) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5816 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5829 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5855  ->
                                  match uu____5855 with
                                  | (arg,uu____5863) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5867 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5867)) in
                      FStar_All.pipe_right uu____5829 FStar_List.flatten in
                let pat_term1 uu____5883 = encode_term pat_term env1 in
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
      let uu____5890 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5914  ->
                fun uu____5915  ->
                  match (uu____5914, uu____5915) with
                  | ((tms,decls),(t,uu____5935)) ->
                      let uu____5946 = encode_term t env in
                      (match uu____5946 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5890 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5980 = FStar_Syntax_Util.list_elements e in
        match uu____5980 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5995 =
          let uu____6005 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____6005 FStar_Syntax_Util.head_and_args in
        match uu____5995 with
        | (head1,args) ->
            let uu____6033 =
              let uu____6041 =
                let uu____6042 = FStar_Syntax_Util.un_uinst head1 in
                uu____6042.FStar_Syntax_Syntax.n in
              (uu____6041, args) in
            (match uu____6033 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6053,uu____6054)::(e,uu____6056)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____6082 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6109 =
            let uu____6119 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6119 FStar_Syntax_Util.head_and_args in
          match uu____6109 with
          | (head1,args) ->
              let uu____6148 =
                let uu____6156 =
                  let uu____6157 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6157.FStar_Syntax_Syntax.n in
                (uu____6156, args) in
              (match uu____6148 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6170)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____6190 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____6205 = smt_pat_or1 t1 in
            (match uu____6205 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____6218 = list_elements1 e in
                 FStar_All.pipe_right uu____6218
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6231 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6231
                           (FStar_List.map one_pat)))
             | uu____6239 ->
                 let uu____6243 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6243])
        | uu____6259 ->
            let uu____6261 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6261] in
      let uu____6277 =
        let uu____6290 =
          let uu____6291 = FStar_Syntax_Subst.compress t in
          uu____6291.FStar_Syntax_Syntax.n in
        match uu____6290 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6318 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6318 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6347;
                        FStar_Syntax_Syntax.effect_name = uu____6348;
                        FStar_Syntax_Syntax.result_typ = uu____6349;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6351)::(post,uu____6353)::(pats,uu____6355)::[];
                        FStar_Syntax_Syntax.flags = uu____6356;_}
                      ->
                      let uu____6388 = lemma_pats pats in
                      (binders1, pre, post, uu____6388)
                  | uu____6401 -> failwith "impos"))
        | uu____6414 -> failwith "Impos" in
      match uu____6277 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6450 = env in
            {
              bindings = (uu___136_6450.bindings);
              depth = (uu___136_6450.depth);
              tcenv = (uu___136_6450.tcenv);
              warn = (uu___136_6450.warn);
              cache = (uu___136_6450.cache);
              nolabels = (uu___136_6450.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6450.encode_non_total_function_typ);
              current_module_name = (uu___136_6450.current_module_name)
            } in
          let uu____6451 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____6451 with
           | (vars,guards,env2,decls,uu____6466) ->
               let uu____6473 =
                 let uu____6480 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6506 =
                             let uu____6511 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6511 FStar_List.unzip in
                           match uu____6506 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6480 FStar_List.unzip in
               (match uu____6473 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6570 = env2 in
                      {
                        bindings = (uu___137_6570.bindings);
                        depth = (uu___137_6570.depth);
                        tcenv = (uu___137_6570.tcenv);
                        warn = (uu___137_6570.warn);
                        cache = (uu___137_6570.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6570.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6570.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6570.current_module_name)
                      } in
                    let uu____6571 =
                      let uu____6574 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6574 env3 in
                    (match uu____6571 with
                     | (pre1,decls'') ->
                         let uu____6579 =
                           let uu____6582 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6582 env3 in
                         (match uu____6579 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6589 =
                                let uu____6590 =
                                  let uu____6596 =
                                    let uu____6597 =
                                      let uu____6600 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6600, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6597 in
                                  (pats, vars, uu____6596) in
                                FStar_SMTEncoding_Util.mkForall uu____6590 in
                              (uu____6589, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6613 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6613
        then
          let uu____6614 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6615 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6614 uu____6615
        else () in
      let enc f r l =
        let uu____6642 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6660 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____6660 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6642 with
        | (decls,args) ->
            let uu____6677 =
              let uu___138_6678 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6678.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6678.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6677, decls) in
      let const_op f r uu____6703 = let uu____6712 = f r in (uu____6712, []) in
      let un_op f l =
        let uu____6728 = FStar_List.hd l in FStar_All.pipe_left f uu____6728 in
      let bin_op f uu___112_6741 =
        match uu___112_6741 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6749 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6776 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6792  ->
                 match uu____6792 with
                 | (t,uu____6800) ->
                     let uu____6801 = encode_formula t env in
                     (match uu____6801 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6776 with
        | (decls,phis) ->
            let uu____6818 =
              let uu___139_6819 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6819.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6819.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6818, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6862  ->
               match uu____6862 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____6876) -> false
                    | uu____6877 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6890 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6890
        else
          (let uu____6905 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6905 r rf) in
      let mk_imp1 r uu___113_6924 =
        match uu___113_6924 with
        | (lhs,uu____6928)::(rhs,uu____6930)::[] ->
            let uu____6951 = encode_formula rhs env in
            (match uu____6951 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6960) ->
                      (l1, decls1)
                  | uu____6963 ->
                      let uu____6964 = encode_formula lhs env in
                      (match uu____6964 with
                       | (l2,decls2) ->
                           let uu____6971 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6971, (FStar_List.append decls1 decls2)))))
        | uu____6973 -> failwith "impossible" in
      let mk_ite r uu___114_6988 =
        match uu___114_6988 with
        | (guard,uu____6992)::(_then,uu____6994)::(_else,uu____6996)::[] ->
            let uu____7025 = encode_formula guard env in
            (match uu____7025 with
             | (g,decls1) ->
                 let uu____7032 = encode_formula _then env in
                 (match uu____7032 with
                  | (t,decls2) ->
                      let uu____7039 = encode_formula _else env in
                      (match uu____7039 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7048 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7067 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7067 in
      let connectives =
        let uu____7079 =
          let uu____7088 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____7088) in
        let uu____7101 =
          let uu____7111 =
            let uu____7120 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____7120) in
          let uu____7133 =
            let uu____7143 =
              let uu____7153 =
                let uu____7162 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____7162) in
              let uu____7175 =
                let uu____7185 =
                  let uu____7195 =
                    let uu____7204 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____7204) in
                  [uu____7195;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____7185 in
              uu____7153 :: uu____7175 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____7143 in
          uu____7111 :: uu____7133 in
        uu____7079 :: uu____7101 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7420 = encode_formula phi' env in
            (match uu____7420 with
             | (phi2,decls) ->
                 let uu____7427 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7427, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7428 ->
            let uu____7433 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7433 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7460 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7460 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7468;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7470;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7486 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7486 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7518::(x,uu____7520)::(t,uu____7522)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____7556 = encode_term x env in
                 (match uu____7556 with
                  | (x1,decls) ->
                      let uu____7563 = encode_term t env in
                      (match uu____7563 with
                       | (t1,decls') ->
                           let uu____7570 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7570, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7574)::(msg,uu____7576)::(phi2,uu____7578)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____7612 =
                   let uu____7615 =
                     let uu____7616 = FStar_Syntax_Subst.compress r in
                     uu____7616.FStar_Syntax_Syntax.n in
                   let uu____7619 =
                     let uu____7620 = FStar_Syntax_Subst.compress msg in
                     uu____7620.FStar_Syntax_Syntax.n in
                   (uu____7615, uu____7619) in
                 (match uu____7612 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7627))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1 in
                      fallback phi3
                  | uu____7639 -> fallback phi2)
             | uu____7642 when head_redex env head2 ->
                 let uu____7650 = whnf env phi1 in
                 encode_formula uu____7650 env
             | uu____7651 ->
                 let uu____7659 = encode_term phi1 env in
                 (match uu____7659 with
                  | (tt,decls) ->
                      let uu____7666 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7669 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7669.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7669.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7666, decls)))
        | uu____7672 ->
            let uu____7673 = encode_term phi1 env in
            (match uu____7673 with
             | (tt,decls) ->
                 let uu____7680 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7683 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7683.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7683.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7680, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7710 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____7710 with
        | (vars,guards,env2,decls,uu____7732) ->
            let uu____7739 =
              let uu____7746 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7773 =
                          let uu____7778 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7795  ->
                                    match uu____7795 with
                                    | (t,uu____7801) ->
                                        encode_term t
                                          (let uu___142_7803 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7803.bindings);
                                             depth = (uu___142_7803.depth);
                                             tcenv = (uu___142_7803.tcenv);
                                             warn = (uu___142_7803.warn);
                                             cache = (uu___142_7803.cache);
                                             nolabels =
                                               (uu___142_7803.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7803.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7803.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7778 FStar_List.unzip in
                        match uu____7773 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7746 FStar_List.unzip in
            (match uu____7739 with
             | (pats,decls') ->
                 let uu____7855 = encode_formula body env2 in
                 (match uu____7855 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7874;
                             FStar_SMTEncoding_Term.rng = uu____7875;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____7883 -> guards in
                      let uu____7886 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7886, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7923  ->
                   match uu____7923 with
                   | (x,uu____7927) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7933 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7942 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7942) uu____7933 tl1 in
             let uu____7944 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7960  ->
                       match uu____7960 with
                       | (b,uu____7964) ->
                           let uu____7965 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7965)) in
             (match uu____7944 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____7969) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7981 =
                    let uu____7982 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7982 in
                  FStar_Errors.warn pos uu____7981) in
       let uu____7983 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7983 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____7989 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____8028  ->
                     match uu____8028 with
                     | (l,uu____8038) -> FStar_Ident.lid_equals op l)) in
           (match uu____7989 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____8061,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8090 = encode_q_body env vars pats body in
             match uu____8090 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8116 =
                     let uu____8122 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8122) in
                   FStar_SMTEncoding_Term.mkForall uu____8116
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8134 = encode_q_body env vars pats body in
             match uu____8134 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8159 =
                   let uu____8160 =
                     let uu____8166 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8166) in
                   FStar_SMTEncoding_Term.mkExists uu____8160
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8159, decls))))
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
  let uu____8245 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8245 with
  | (asym,a) ->
      let uu____8250 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8250 with
       | (xsym,x) ->
           let uu____8255 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8255 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8285 =
                      let uu____8291 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____8291, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8285 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____8306 =
                      let uu____8310 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8310) in
                    FStar_SMTEncoding_Util.mkApp uu____8306 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8318 =
                    let uu____8320 =
                      let uu____8322 =
                        let uu____8324 =
                          let uu____8325 =
                            let uu____8329 =
                              let uu____8330 =
                                let uu____8336 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8336) in
                              FStar_SMTEncoding_Util.mkForall uu____8330 in
                            (uu____8329, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8325 in
                        let uu____8345 =
                          let uu____8347 =
                            let uu____8348 =
                              let uu____8352 =
                                let uu____8353 =
                                  let uu____8359 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____8359) in
                                FStar_SMTEncoding_Util.mkForall uu____8353 in
                              (uu____8352,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____8348 in
                          [uu____8347] in
                        uu____8324 :: uu____8345 in
                      xtok_decl :: uu____8322 in
                    xname_decl :: uu____8320 in
                  (xtok1, uu____8318) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____8408 =
                    let uu____8416 =
                      let uu____8422 =
                        let uu____8423 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8423 in
                      quant axy uu____8422 in
                    (FStar_Parser_Const.op_Eq, uu____8416) in
                  let uu____8429 =
                    let uu____8438 =
                      let uu____8446 =
                        let uu____8452 =
                          let uu____8453 =
                            let uu____8454 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8454 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8453 in
                        quant axy uu____8452 in
                      (FStar_Parser_Const.op_notEq, uu____8446) in
                    let uu____8460 =
                      let uu____8469 =
                        let uu____8477 =
                          let uu____8483 =
                            let uu____8484 =
                              let uu____8485 =
                                let uu____8488 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8489 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8488, uu____8489) in
                              FStar_SMTEncoding_Util.mkLT uu____8485 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8484 in
                          quant xy uu____8483 in
                        (FStar_Parser_Const.op_LT, uu____8477) in
                      let uu____8495 =
                        let uu____8504 =
                          let uu____8512 =
                            let uu____8518 =
                              let uu____8519 =
                                let uu____8520 =
                                  let uu____8523 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8524 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8523, uu____8524) in
                                FStar_SMTEncoding_Util.mkLTE uu____8520 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8519 in
                            quant xy uu____8518 in
                          (FStar_Parser_Const.op_LTE, uu____8512) in
                        let uu____8530 =
                          let uu____8539 =
                            let uu____8547 =
                              let uu____8553 =
                                let uu____8554 =
                                  let uu____8555 =
                                    let uu____8558 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8559 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8558, uu____8559) in
                                  FStar_SMTEncoding_Util.mkGT uu____8555 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8554 in
                              quant xy uu____8553 in
                            (FStar_Parser_Const.op_GT, uu____8547) in
                          let uu____8565 =
                            let uu____8574 =
                              let uu____8582 =
                                let uu____8588 =
                                  let uu____8589 =
                                    let uu____8590 =
                                      let uu____8593 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8594 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8593, uu____8594) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8590 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8589 in
                                quant xy uu____8588 in
                              (FStar_Parser_Const.op_GTE, uu____8582) in
                            let uu____8600 =
                              let uu____8609 =
                                let uu____8617 =
                                  let uu____8623 =
                                    let uu____8624 =
                                      let uu____8625 =
                                        let uu____8628 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8629 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8628, uu____8629) in
                                      FStar_SMTEncoding_Util.mkSub uu____8625 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8624 in
                                  quant xy uu____8623 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____8617) in
                              let uu____8635 =
                                let uu____8644 =
                                  let uu____8652 =
                                    let uu____8658 =
                                      let uu____8659 =
                                        let uu____8660 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8660 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8659 in
                                    quant qx uu____8658 in
                                  (FStar_Parser_Const.op_Minus, uu____8652) in
                                let uu____8666 =
                                  let uu____8675 =
                                    let uu____8683 =
                                      let uu____8689 =
                                        let uu____8690 =
                                          let uu____8691 =
                                            let uu____8694 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8695 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8694, uu____8695) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8691 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8690 in
                                      quant xy uu____8689 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____8683) in
                                  let uu____8701 =
                                    let uu____8710 =
                                      let uu____8718 =
                                        let uu____8724 =
                                          let uu____8725 =
                                            let uu____8726 =
                                              let uu____8729 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8730 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8729, uu____8730) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8726 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8725 in
                                        quant xy uu____8724 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____8718) in
                                    let uu____8736 =
                                      let uu____8745 =
                                        let uu____8753 =
                                          let uu____8759 =
                                            let uu____8760 =
                                              let uu____8761 =
                                                let uu____8764 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8765 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8764, uu____8765) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8761 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8760 in
                                          quant xy uu____8759 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____8753) in
                                      let uu____8771 =
                                        let uu____8780 =
                                          let uu____8788 =
                                            let uu____8794 =
                                              let uu____8795 =
                                                let uu____8796 =
                                                  let uu____8799 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8800 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8799, uu____8800) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8796 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8795 in
                                            quant xy uu____8794 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____8788) in
                                        let uu____8806 =
                                          let uu____8815 =
                                            let uu____8823 =
                                              let uu____8829 =
                                                let uu____8830 =
                                                  let uu____8831 =
                                                    let uu____8834 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8835 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8834, uu____8835) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8831 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8830 in
                                              quant xy uu____8829 in
                                            (FStar_Parser_Const.op_And,
                                              uu____8823) in
                                          let uu____8841 =
                                            let uu____8850 =
                                              let uu____8858 =
                                                let uu____8864 =
                                                  let uu____8865 =
                                                    let uu____8866 =
                                                      let uu____8869 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8870 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8869,
                                                        uu____8870) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8866 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8865 in
                                                quant xy uu____8864 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____8858) in
                                            let uu____8876 =
                                              let uu____8885 =
                                                let uu____8893 =
                                                  let uu____8899 =
                                                    let uu____8900 =
                                                      let uu____8901 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8901 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8900 in
                                                  quant qx uu____8899 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____8893) in
                                              [uu____8885] in
                                            uu____8850 :: uu____8876 in
                                          uu____8815 :: uu____8841 in
                                        uu____8780 :: uu____8806 in
                                      uu____8745 :: uu____8771 in
                                    uu____8710 :: uu____8736 in
                                  uu____8675 :: uu____8701 in
                                uu____8644 :: uu____8666 in
                              uu____8609 :: uu____8635 in
                            uu____8574 :: uu____8600 in
                          uu____8539 :: uu____8565 in
                        uu____8504 :: uu____8530 in
                      uu____8469 :: uu____8495 in
                    uu____8438 :: uu____8460 in
                  uu____8408 :: uu____8429 in
                let mk1 l v1 =
                  let uu____9029 =
                    let uu____9034 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9069  ->
                              match uu____9069 with
                              | (l',uu____9078) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____9034
                      (FStar_Option.map
                         (fun uu____9114  ->
                            match uu____9114 with | (uu____9125,b) -> b v1)) in
                  FStar_All.pipe_right uu____9029 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9169  ->
                          match uu____9169 with
                          | (l',uu____9178) -> FStar_Ident.lid_equals l l')) in
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
        let uu____9207 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9207 with
        | (xxsym,xx) ->
            let uu____9212 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9212 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____9220 =
                   let uu____9224 =
                     let uu____9225 =
                       let uu____9231 =
                         let uu____9232 =
                           let uu____9235 =
                             let uu____9236 =
                               let uu____9239 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9239) in
                             FStar_SMTEncoding_Util.mkEq uu____9236 in
                           (xx_has_type, uu____9235) in
                         FStar_SMTEncoding_Util.mkImp uu____9232 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9231) in
                     FStar_SMTEncoding_Util.mkForall uu____9225 in
                   let uu____9252 =
                     let uu____9253 =
                       let uu____9254 =
                         let uu____9255 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9255 in
                       Prims.strcat module_name uu____9254 in
                     varops.mk_unique uu____9253 in
                   (uu____9224, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____9252) in
                 FStar_SMTEncoding_Util.mkAssume uu____9220)
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
    let uu____9289 =
      let uu____9290 =
        let uu____9294 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9294, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9290 in
    let uu____9296 =
      let uu____9298 =
        let uu____9299 =
          let uu____9303 =
            let uu____9304 =
              let uu____9310 =
                let uu____9311 =
                  let uu____9314 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9314) in
                FStar_SMTEncoding_Util.mkImp uu____9311 in
              ([[typing_pred]], [xx], uu____9310) in
            mkForall_fuel uu____9304 in
          (uu____9303, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9299 in
      [uu____9298] in
    uu____9289 :: uu____9296 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9342 =
      let uu____9343 =
        let uu____9347 =
          let uu____9348 =
            let uu____9354 =
              let uu____9357 =
                let uu____9359 = FStar_SMTEncoding_Term.boxBool b in
                [uu____9359] in
              [uu____9357] in
            let uu____9362 =
              let uu____9363 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____9363 tt in
            (uu____9354, [bb], uu____9362) in
          FStar_SMTEncoding_Util.mkForall uu____9348 in
        (uu____9347, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9343 in
    let uu____9374 =
      let uu____9376 =
        let uu____9377 =
          let uu____9381 =
            let uu____9382 =
              let uu____9388 =
                let uu____9389 =
                  let uu____9392 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____9392) in
                FStar_SMTEncoding_Util.mkImp uu____9389 in
              ([[typing_pred]], [xx], uu____9388) in
            mkForall_fuel uu____9382 in
          (uu____9381, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9377 in
      [uu____9376] in
    uu____9342 :: uu____9374 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____9426 =
        let uu____9427 =
          let uu____9431 =
            let uu____9433 =
              let uu____9435 =
                let uu____9437 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9438 =
                  let uu____9440 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9440] in
                uu____9437 :: uu____9438 in
              tt :: uu____9435 in
            tt :: uu____9433 in
          ("Prims.Precedes", uu____9431) in
        FStar_SMTEncoding_Util.mkApp uu____9427 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9426 in
    let precedes_y_x =
      let uu____9443 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9443 in
    let uu____9445 =
      let uu____9446 =
        let uu____9450 =
          let uu____9451 =
            let uu____9457 =
              let uu____9460 =
                let uu____9462 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9462] in
              [uu____9460] in
            let uu____9465 =
              let uu____9466 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9466 tt in
            (uu____9457, [bb], uu____9465) in
          FStar_SMTEncoding_Util.mkForall uu____9451 in
        (uu____9450, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9446 in
    let uu____9477 =
      let uu____9479 =
        let uu____9480 =
          let uu____9484 =
            let uu____9485 =
              let uu____9491 =
                let uu____9492 =
                  let uu____9495 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9495) in
                FStar_SMTEncoding_Util.mkImp uu____9492 in
              ([[typing_pred]], [xx], uu____9491) in
            mkForall_fuel uu____9485 in
          (uu____9484, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9480 in
      let uu____9508 =
        let uu____9510 =
          let uu____9511 =
            let uu____9515 =
              let uu____9516 =
                let uu____9522 =
                  let uu____9523 =
                    let uu____9526 =
                      let uu____9527 =
                        let uu____9529 =
                          let uu____9531 =
                            let uu____9533 =
                              let uu____9534 =
                                let uu____9537 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9538 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9537, uu____9538) in
                              FStar_SMTEncoding_Util.mkGT uu____9534 in
                            let uu____9539 =
                              let uu____9541 =
                                let uu____9542 =
                                  let uu____9545 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9546 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9545, uu____9546) in
                                FStar_SMTEncoding_Util.mkGTE uu____9542 in
                              let uu____9547 =
                                let uu____9549 =
                                  let uu____9550 =
                                    let uu____9553 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9554 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9553, uu____9554) in
                                  FStar_SMTEncoding_Util.mkLT uu____9550 in
                                [uu____9549] in
                              uu____9541 :: uu____9547 in
                            uu____9533 :: uu____9539 in
                          typing_pred_y :: uu____9531 in
                        typing_pred :: uu____9529 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9527 in
                    (uu____9526, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9523 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9522) in
              mkForall_fuel uu____9516 in
            (uu____9515,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9511 in
        [uu____9510] in
      uu____9479 :: uu____9508 in
    uu____9445 :: uu____9477 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9584 =
      let uu____9585 =
        let uu____9589 =
          let uu____9590 =
            let uu____9596 =
              let uu____9599 =
                let uu____9601 = FStar_SMTEncoding_Term.boxString b in
                [uu____9601] in
              [uu____9599] in
            let uu____9604 =
              let uu____9605 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9605 tt in
            (uu____9596, [bb], uu____9604) in
          FStar_SMTEncoding_Util.mkForall uu____9590 in
        (uu____9589, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9585 in
    let uu____9616 =
      let uu____9618 =
        let uu____9619 =
          let uu____9623 =
            let uu____9624 =
              let uu____9630 =
                let uu____9631 =
                  let uu____9634 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9634) in
                FStar_SMTEncoding_Util.mkImp uu____9631 in
              ([[typing_pred]], [xx], uu____9630) in
            mkForall_fuel uu____9624 in
          (uu____9623, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9619 in
      [uu____9618] in
    uu____9584 :: uu____9616 in
  let mk_ref1 env reft_name uu____9656 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9667 =
        let uu____9671 =
          let uu____9673 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9673] in
        (reft_name, uu____9671) in
      FStar_SMTEncoding_Util.mkApp uu____9667 in
    let refb =
      let uu____9676 =
        let uu____9680 =
          let uu____9682 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9682] in
        (reft_name, uu____9680) in
      FStar_SMTEncoding_Util.mkApp uu____9676 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9686 =
      let uu____9687 =
        let uu____9691 =
          let uu____9692 =
            let uu____9698 =
              let uu____9699 =
                let uu____9702 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9702) in
              FStar_SMTEncoding_Util.mkImp uu____9699 in
            ([[typing_pred]], [xx; aa], uu____9698) in
          mkForall_fuel uu____9692 in
        (uu____9691, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9687 in
    [uu____9686] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9742 =
      let uu____9743 =
        let uu____9747 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9747, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9743 in
    [uu____9742] in
  let mk_and_interp env conj uu____9758 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9775 =
      let uu____9776 =
        let uu____9780 =
          let uu____9781 =
            let uu____9787 =
              let uu____9788 =
                let uu____9791 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9791, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9788 in
            ([[l_and_a_b]], [aa; bb], uu____9787) in
          FStar_SMTEncoding_Util.mkForall uu____9781 in
        (uu____9780, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9776 in
    [uu____9775] in
  let mk_or_interp env disj uu____9815 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9832 =
      let uu____9833 =
        let uu____9837 =
          let uu____9838 =
            let uu____9844 =
              let uu____9845 =
                let uu____9848 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9848, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9845 in
            ([[l_or_a_b]], [aa; bb], uu____9844) in
          FStar_SMTEncoding_Util.mkForall uu____9838 in
        (uu____9837, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9833 in
    [uu____9832] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9889 =
      let uu____9890 =
        let uu____9894 =
          let uu____9895 =
            let uu____9901 =
              let uu____9902 =
                let uu____9905 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9905, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9902 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9901) in
          FStar_SMTEncoding_Util.mkForall uu____9895 in
        (uu____9894, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9890 in
    [uu____9889] in
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
    let uu____9952 =
      let uu____9953 =
        let uu____9957 =
          let uu____9958 =
            let uu____9964 =
              let uu____9965 =
                let uu____9968 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9968, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9965 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9964) in
          FStar_SMTEncoding_Util.mkForall uu____9958 in
        (uu____9957, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9953 in
    [uu____9952] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10013 =
      let uu____10014 =
        let uu____10018 =
          let uu____10019 =
            let uu____10025 =
              let uu____10026 =
                let uu____10029 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____10029, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10026 in
            ([[l_imp_a_b]], [aa; bb], uu____10025) in
          FStar_SMTEncoding_Util.mkForall uu____10019 in
        (uu____10018, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10014 in
    [uu____10013] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10070 =
      let uu____10071 =
        let uu____10075 =
          let uu____10076 =
            let uu____10082 =
              let uu____10083 =
                let uu____10086 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10086, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10083 in
            ([[l_iff_a_b]], [aa; bb], uu____10082) in
          FStar_SMTEncoding_Util.mkForall uu____10076 in
        (uu____10075, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10071 in
    [uu____10070] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____10120 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10120 in
    let uu____10122 =
      let uu____10123 =
        let uu____10127 =
          let uu____10128 =
            let uu____10134 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10134) in
          FStar_SMTEncoding_Util.mkForall uu____10128 in
        (uu____10127, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10123 in
    [uu____10122] in
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
      let uu____10174 =
        let uu____10178 =
          let uu____10180 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10180] in
        ("Valid", uu____10178) in
      FStar_SMTEncoding_Util.mkApp uu____10174 in
    let uu____10182 =
      let uu____10183 =
        let uu____10187 =
          let uu____10188 =
            let uu____10194 =
              let uu____10195 =
                let uu____10198 =
                  let uu____10199 =
                    let uu____10205 =
                      let uu____10208 =
                        let uu____10210 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10210] in
                      [uu____10208] in
                    let uu____10213 =
                      let uu____10214 =
                        let uu____10217 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10217, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10214 in
                    (uu____10205, [xx1], uu____10213) in
                  FStar_SMTEncoding_Util.mkForall uu____10199 in
                (uu____10198, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10195 in
            ([[l_forall_a_b]], [aa; bb], uu____10194) in
          FStar_SMTEncoding_Util.mkForall uu____10188 in
        (uu____10187, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10183 in
    [uu____10182] in
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
      let uu____10268 =
        let uu____10272 =
          let uu____10274 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10274] in
        ("Valid", uu____10272) in
      FStar_SMTEncoding_Util.mkApp uu____10268 in
    let uu____10276 =
      let uu____10277 =
        let uu____10281 =
          let uu____10282 =
            let uu____10288 =
              let uu____10289 =
                let uu____10292 =
                  let uu____10293 =
                    let uu____10299 =
                      let uu____10302 =
                        let uu____10304 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10304] in
                      [uu____10302] in
                    let uu____10307 =
                      let uu____10308 =
                        let uu____10311 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10311, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10308 in
                    (uu____10299, [xx1], uu____10307) in
                  FStar_SMTEncoding_Util.mkExists uu____10293 in
                (uu____10292, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10289 in
            ([[l_exists_a_b]], [aa; bb], uu____10288) in
          FStar_SMTEncoding_Util.mkForall uu____10282 in
        (uu____10281, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10277 in
    [uu____10276] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____10347 =
      let uu____10348 =
        let uu____10352 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____10353 = varops.mk_unique "typing_range_const" in
        (uu____10352, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____10353) in
      FStar_SMTEncoding_Util.mkAssume uu____10348 in
    [uu____10347] in
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
          let uu____10615 =
            FStar_Util.find_opt
              (fun uu____10636  ->
                 match uu____10636 with
                 | (l,uu____10646) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10615 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____10668,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10704 = encode_function_type_as_formula t env in
        match uu____10704 with
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
            let uu____10737 =
              (let uu____10740 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10740) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10737
            then
              let uu____10744 = new_term_constant_and_tok_from_lid env lid in
              match uu____10744 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10756 =
                      let uu____10757 = FStar_Syntax_Subst.compress t_norm in
                      uu____10757.FStar_Syntax_Syntax.n in
                    match uu____10756 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10762) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10780  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10783 -> [] in
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
              (let uu____10792 = prims.is lid in
               if uu____10792
               then
                 let vname = varops.new_fvar lid in
                 let uu____10797 = prims.mk lid vname in
                 match uu____10797 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10812 =
                    let uu____10818 = curried_arrow_formals_comp t_norm in
                    match uu____10818 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10829 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10829
                          then
                            let uu____10830 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10833 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10833.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10833.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10833.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10833.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10833.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10833.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10833.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10833.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10833.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10833.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10833.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10833.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10833.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10833.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10833.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10833.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10833.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10833.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10833.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10833.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10833.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10833.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10833.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10833.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10833.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10833.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10830
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10840 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10840)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10812 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10867 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10867 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10880 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10912  ->
                                     match uu___115_10912 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10915 =
                                           FStar_Util.prefix vars in
                                         (match uu____10915 with
                                          | (uu____10926,(xxsym,uu____10928))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10938 =
                                                let uu____10939 =
                                                  let uu____10943 =
                                                    let uu____10944 =
                                                      let uu____10950 =
                                                        let uu____10951 =
                                                          let uu____10954 =
                                                            let uu____10955 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10955 in
                                                          (vapp, uu____10954) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10951 in
                                                      ([[vapp]], vars,
                                                        uu____10950) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10944 in
                                                  (uu____10943,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10939 in
                                              [uu____10938])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10966 =
                                           FStar_Util.prefix vars in
                                         (match uu____10966 with
                                          | (uu____10977,(xxsym,uu____10979))
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
                                              let uu____10993 =
                                                let uu____10994 =
                                                  let uu____10998 =
                                                    let uu____10999 =
                                                      let uu____11005 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____11005) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10999 in
                                                  (uu____10998,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10994 in
                                              [uu____10993])
                                     | uu____11014 -> [])) in
                           let uu____11015 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____11015 with
                            | (vars,guards,env',decls1,uu____11031) ->
                                let uu____11038 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____11043 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____11043, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____11045 = encode_formula p env' in
                                      (match uu____11045 with
                                       | (g,ds) ->
                                           let uu____11052 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____11052,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____11038 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____11061 =
                                         let uu____11065 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____11065) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____11061 in
                                     let uu____11070 =
                                       let vname_decl =
                                         let uu____11075 =
                                           let uu____11081 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11087  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11081,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____11075 in
                                       let uu____11092 =
                                         let env2 =
                                           let uu___144_11096 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11096.bindings);
                                             depth = (uu___144_11096.depth);
                                             tcenv = (uu___144_11096.tcenv);
                                             warn = (uu___144_11096.warn);
                                             cache = (uu___144_11096.cache);
                                             nolabels =
                                               (uu___144_11096.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11096.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11096.current_module_name)
                                           } in
                                         let uu____11097 =
                                           let uu____11098 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11098 in
                                         if uu____11097
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____11092 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11108::uu____11109 ->
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
                                                   let uu____11132 =
                                                     let uu____11138 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11138) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11132 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11152 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____11154 =
                                             match formals with
                                             | [] ->
                                                 let uu____11163 =
                                                   let uu____11164 =
                                                     let uu____11166 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_41)
                                                       uu____11166 in
                                                   push_free_var env1 lid
                                                     vname uu____11164 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11163)
                                             | uu____11169 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____11174 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11174 in
                                                 let name_tok_corr =
                                                   let uu____11176 =
                                                     let uu____11180 =
                                                       let uu____11181 =
                                                         let uu____11187 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11187) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11181 in
                                                     (uu____11180,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11176 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____11154 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____11070 with
                                      | (decls2,env2) ->
                                          let uu____11211 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11216 =
                                              encode_term res_t1 env' in
                                            match uu____11216 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11224 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11224,
                                                  decls) in
                                          (match uu____11211 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11232 =
                                                   let uu____11236 =
                                                     let uu____11237 =
                                                       let uu____11243 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11243) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11237 in
                                                   (uu____11236,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11232 in
                                               let freshness =
                                                 let uu____11252 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11252
                                                 then
                                                   let uu____11255 =
                                                     let uu____11256 =
                                                       let uu____11262 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____11268 =
                                                         varops.next_id () in
                                                       (vname, uu____11262,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11268) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11256 in
                                                   let uu____11270 =
                                                     let uu____11272 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11272] in
                                                   uu____11255 :: uu____11270
                                                 else [] in
                                               let g =
                                                 let uu____11276 =
                                                   let uu____11278 =
                                                     let uu____11280 =
                                                       let uu____11282 =
                                                         let uu____11284 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____11284 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11282 in
                                                     FStar_List.append decls3
                                                       uu____11280 in
                                                   FStar_List.append decls2
                                                     uu____11278 in
                                                 FStar_List.append decls11
                                                   uu____11276 in
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
          let uu____11310 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11310 with
          | FStar_Pervasives_Native.None  ->
              let uu____11329 = encode_free_var env x t t_norm [] in
              (match uu____11329 with
               | (decls,env1) ->
                   let uu____11344 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____11344 with
                    | (n1,x',uu____11359) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____11371) ->
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
          let uu____11408 = encode_free_var env lid t tt quals in
          match uu____11408 with
          | (decls,env1) ->
              let uu____11419 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____11419
              then
                let uu____11423 =
                  let uu____11425 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11425 in
                (uu____11423, env1)
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
             (fun uu____11463  ->
                fun lb  ->
                  match uu____11463 with
                  | (decls,env1) ->
                      let uu____11475 =
                        let uu____11479 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11479
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11475 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____11494 = FStar_Syntax_Util.head_and_args t in
    match uu____11494 with
    | (hd1,args) ->
        let uu____11520 =
          let uu____11521 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11521.FStar_Syntax_Syntax.n in
        (match uu____11520 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11525,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11538 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____11556  ->
      fun quals  ->
        match uu____11556 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11606 = FStar_Util.first_N nbinders formals in
              match uu____11606 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11655  ->
                         fun uu____11656  ->
                           match (uu____11655, uu____11656) with
                           | ((formal,uu____11666),(binder,uu____11668)) ->
                               let uu____11673 =
                                 let uu____11678 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11678) in
                               FStar_Syntax_Syntax.NT uu____11673) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11683 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11701  ->
                              match uu____11701 with
                              | (x,i) ->
                                  let uu____11708 =
                                    let uu___145_11709 = x in
                                    let uu____11710 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11709.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11709.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11710
                                    } in
                                  (uu____11708, i))) in
                    FStar_All.pipe_right uu____11683
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11722 =
                      let uu____11724 =
                        let uu____11725 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11725.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_42  -> FStar_Pervasives_Native.Some _0_42)
                        uu____11724 in
                    let uu____11729 =
                      let uu____11730 = FStar_Syntax_Subst.compress body in
                      let uu____11731 =
                        let uu____11732 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____11732 in
                      FStar_Syntax_Syntax.extend_app_n uu____11730
                        uu____11731 in
                    uu____11729 uu____11722 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11774 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11774
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11777 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11777.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11777.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11777.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11777.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11777.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11777.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11777.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11777.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11777.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11777.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11777.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11777.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11777.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11777.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11777.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11777.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11777.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11777.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11777.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11777.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11777.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11777.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11777.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11777.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11777.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11777.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11798 = FStar_Syntax_Util.abs_formals e in
                match uu____11798 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11832::uu____11833 ->
                         let uu____11841 =
                           let uu____11842 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11842.FStar_Syntax_Syntax.n in
                         (match uu____11841 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11869 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11869 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11897 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11897
                                   then
                                     let uu____11920 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11920 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11975  ->
                                                   fun uu____11976  ->
                                                     match (uu____11975,
                                                             uu____11976)
                                                     with
                                                     | ((x,uu____11986),
                                                        (b,uu____11988)) ->
                                                         let uu____11993 =
                                                           let uu____11998 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11998) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11993)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____12000 =
                                            let uu____12011 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____12011) in
                                          (uu____12000, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____12051 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____12051 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12103) ->
                              let uu____12108 =
                                let uu____12119 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____12119 in
                              (uu____12108, true)
                          | uu____12152 when Prims.op_Negation norm1 ->
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
                          | uu____12154 ->
                              let uu____12155 =
                                let uu____12156 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12157 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12156
                                  uu____12157 in
                              failwith uu____12155)
                     | uu____12170 ->
                         let uu____12171 =
                           let uu____12172 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12172.FStar_Syntax_Syntax.n in
                         (match uu____12171 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12199 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12199 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12217 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12217 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12265 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12295 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____12295
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12303 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____12357  ->
                            fun lb  ->
                              match uu____12357 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____12408 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____12408
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____12411 =
                                      let uu____12419 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____12419
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____12411 with
                                    | (tok,decl,env2) ->
                                        let uu____12444 =
                                          let uu____12451 =
                                            let uu____12457 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12457, tok) in
                                          uu____12451 :: toks in
                                        (uu____12444, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12303 with
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
                        | uu____12559 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____12564 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12564 vars)
                            else
                              (let uu____12566 =
                                 let uu____12570 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12570) in
                               FStar_SMTEncoding_Util.mkApp uu____12566) in
                      let uu____12575 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_12578  ->
                                 match uu___116_12578 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12579 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12584 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12584))) in
                      if uu____12575
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12604;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12606;
                                FStar_Syntax_Syntax.lbeff = uu____12607;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12644 =
                                 let uu____12648 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12648 with
                                 | (tcenv',uu____12659,e_t) ->
                                     let uu____12663 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12670 -> failwith "Impossible" in
                                     (match uu____12663 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12680 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12680.bindings);
                                              depth = (uu___149_12680.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12680.warn);
                                              cache = (uu___149_12680.cache);
                                              nolabels =
                                                (uu___149_12680.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12680.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12680.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12680.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12644 with
                                | (env',e1,t_norm1) ->
                                    let uu____12687 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12687 with
                                     | ((binders,body,uu____12699,uu____12700),curry)
                                         ->
                                         ((let uu____12707 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12707
                                           then
                                             let uu____12708 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12709 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12708 uu____12709
                                           else ());
                                          (let uu____12711 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____12711 with
                                           | (vars,guards,env'1,binder_decls,uu____12727)
                                               ->
                                               let body1 =
                                                 let uu____12735 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12735
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12738 =
                                                 let uu____12743 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12743
                                                 then
                                                   let uu____12749 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12750 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12749, uu____12750)
                                                 else
                                                   (let uu____12756 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12756)) in
                                               (match uu____12738 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12770 =
                                                        let uu____12774 =
                                                          let uu____12775 =
                                                            let uu____12781 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12781) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12775 in
                                                        let uu____12787 =
                                                          let uu____12789 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____12789 in
                                                        (uu____12774,
                                                          uu____12787,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12770 in
                                                    let uu____12791 =
                                                      let uu____12793 =
                                                        let uu____12795 =
                                                          let uu____12797 =
                                                            let uu____12799 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12799 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12797 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12795 in
                                                      FStar_List.append
                                                        decls1 uu____12793 in
                                                    (uu____12791, env1))))))
                           | uu____12802 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12821 = varops.fresh "fuel" in
                             (uu____12821, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12824 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12874  ->
                                     fun uu____12875  ->
                                       match (uu____12874, uu____12875) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12953 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12953 in
                                           let gtok =
                                             let uu____12955 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12955 in
                                           let env3 =
                                             let uu____12957 =
                                               let uu____12959 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_43) uu____12959 in
                                             push_free_var env2 flid gtok
                                               uu____12957 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12824 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____13045
                                 t_norm uu____13047 =
                                 match (uu____13045, uu____13047) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____13074;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____13075;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____13092 =
                                       let uu____13096 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____13096 with
                                       | (tcenv',uu____13111,e_t) ->
                                           let uu____13115 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13122 ->
                                                 failwith "Impossible" in
                                           (match uu____13115 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13132 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13132.bindings);
                                                    depth =
                                                      (uu___150_13132.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13132.warn);
                                                    cache =
                                                      (uu___150_13132.cache);
                                                    nolabels =
                                                      (uu___150_13132.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13132.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13132.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13132.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____13092 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13142 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____13142
                                            then
                                              let uu____13143 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13144 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13145 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13143 uu____13144
                                                uu____13145
                                            else ());
                                           (let uu____13147 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13147 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13169 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____13169
                                                  then
                                                    let uu____13170 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13171 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13172 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13173 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13170 uu____13171
                                                      uu____13172 uu____13173
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13177 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____13177 with
                                                  | (vars,guards,env'1,binder_decls,uu____13195)
                                                      ->
                                                      let decl_g =
                                                        let uu____13203 =
                                                          let uu____13209 =
                                                            let uu____13211 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13211 in
                                                          (g, uu____13209,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13203 in
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
                                                        let uu____13226 =
                                                          let uu____13230 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13230) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13226 in
                                                      let gsapp =
                                                        let uu____13236 =
                                                          let uu____13240 =
                                                            let uu____13242 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13242 ::
                                                              vars_tm in
                                                          (g, uu____13240) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13236 in
                                                      let gmax =
                                                        let uu____13246 =
                                                          let uu____13250 =
                                                            let uu____13252 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13252 ::
                                                              vars_tm in
                                                          (g, uu____13250) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13246 in
                                                      let body1 =
                                                        let uu____13256 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13256
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____13258 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13258 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13269
                                                               =
                                                               let uu____13273
                                                                 =
                                                                 let uu____13274
                                                                   =
                                                                   let uu____13282
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
                                                                    uu____13282) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13274 in
                                                               let uu____13293
                                                                 =
                                                                 let uu____13295
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____13295 in
                                                               (uu____13273,
                                                                 uu____13293,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13269 in
                                                           let eqn_f =
                                                             let uu____13298
                                                               =
                                                               let uu____13302
                                                                 =
                                                                 let uu____13303
                                                                   =
                                                                   let uu____13309
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13309) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13303 in
                                                               (uu____13302,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13298 in
                                                           let eqn_g' =
                                                             let uu____13317
                                                               =
                                                               let uu____13321
                                                                 =
                                                                 let uu____13322
                                                                   =
                                                                   let uu____13328
                                                                    =
                                                                    let uu____13329
                                                                    =
                                                                    let uu____13332
                                                                    =
                                                                    let uu____13333
                                                                    =
                                                                    let uu____13337
                                                                    =
                                                                    let uu____13339
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____13339
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13337) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13333 in
                                                                    (gsapp,
                                                                    uu____13332) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13329 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13328) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13322 in
                                                               (uu____13321,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13317 in
                                                           let uu____13351 =
                                                             let uu____13356
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____13356
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____13373)
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
                                                                    let uu____13388
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____13388
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____13391
                                                                    =
                                                                    let uu____13395
                                                                    =
                                                                    let uu____13396
                                                                    =
                                                                    let uu____13402
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13402) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13396 in
                                                                    (uu____13395,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13391 in
                                                                 let uu____13413
                                                                   =
                                                                   let uu____13417
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____13417
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____13425
                                                                    =
                                                                    let uu____13427
                                                                    =
                                                                    let uu____13428
                                                                    =
                                                                    let uu____13432
                                                                    =
                                                                    let uu____13433
                                                                    =
                                                                    let uu____13439
                                                                    =
                                                                    let uu____13440
                                                                    =
                                                                    let uu____13443
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____13443,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13440 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13439) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13433 in
                                                                    (uu____13432,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13428 in
                                                                    [uu____13427] in
                                                                    (d3,
                                                                    uu____13425) in
                                                                 (match uu____13413
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____13351
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
                               let uu____13478 =
                                 let uu____13485 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____13533  ->
                                      fun uu____13534  ->
                                        match (uu____13533, uu____13534) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13620 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13620 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13485 in
                               (match uu____13478 with
                                | (decls2,eqns,env01) ->
                                    let uu____13660 =
                                      let isDeclFun uu___117_13668 =
                                        match uu___117_13668 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13669 -> true
                                        | uu____13675 -> false in
                                      let uu____13676 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13676
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13660 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13706 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13706
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
        let uu____13740 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13740 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____13743 = encode_sigelt' env se in
      match uu____13743 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13753 =
                  let uu____13754 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13754 in
                [uu____13753]
            | uu____13755 ->
                let uu____13756 =
                  let uu____13758 =
                    let uu____13759 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13759 in
                  uu____13758 :: g in
                let uu____13760 =
                  let uu____13762 =
                    let uu____13763 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13763 in
                  [uu____13762] in
                FStar_List.append uu____13756 uu____13760 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13773 =
          let uu____13774 = FStar_Syntax_Subst.compress t in
          uu____13774.FStar_Syntax_Syntax.n in
        match uu____13773 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13778)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13781 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13784 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13787 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13789 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13791 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13799 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13802 =
            let uu____13803 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13803 Prims.op_Negation in
          if uu____13802
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13823 ->
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
               let uu____13843 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13843 with
               | (aname,atok,env2) ->
                   let uu____13853 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13853 with
                    | (formals,uu____13863) ->
                        let uu____13870 =
                          let uu____13873 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13873 env2 in
                        (match uu____13870 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13881 =
                                 let uu____13882 =
                                   let uu____13888 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13897  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13888,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13882 in
                               [uu____13881;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____13904 =
                               let aux uu____13933 uu____13934 =
                                 match (uu____13933, uu____13934) with
                                 | ((bv,uu____13961),(env3,acc_sorts,acc)) ->
                                     let uu____13982 = gen_term_var env3 bv in
                                     (match uu____13982 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13904 with
                              | (uu____14020,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____14034 =
                                      let uu____14038 =
                                        let uu____14039 =
                                          let uu____14045 =
                                            let uu____14046 =
                                              let uu____14049 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____14049) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____14046 in
                                          ([[app]], xs_sorts, uu____14045) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14039 in
                                      (uu____14038,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14034 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____14061 =
                                      let uu____14065 =
                                        let uu____14066 =
                                          let uu____14072 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____14072) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14066 in
                                      (uu____14065,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14061 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____14082 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____14082 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14098,uu____14099)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____14100 = new_term_constant_and_tok_from_lid env lid in
          (match uu____14100 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14111,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____14116 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_14119  ->
                      match uu___118_14119 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____14120 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____14123 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14124 -> false)) in
            Prims.op_Negation uu____14116 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____14130 = encode_top_level_val env fv t quals in
             match uu____14130 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____14142 =
                   let uu____14144 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14144 in
                 (uu____14142, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____14150 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____14150 with
           | (uu____14155,f1) ->
               let uu____14157 = encode_formula f1 env in
               (match uu____14157 with
                | (f2,decls) ->
                    let g =
                      let uu____14166 =
                        let uu____14167 =
                          let uu____14171 =
                            let uu____14173 =
                              let uu____14174 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____14174 in
                            FStar_Pervasives_Native.Some uu____14173 in
                          let uu____14175 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____14171, uu____14175) in
                        FStar_SMTEncoding_Util.mkAssume uu____14167 in
                      [uu____14166] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14179) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs in
          let uu____14186 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14201 =
                       let uu____14203 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14203.FStar_Syntax_Syntax.fv_name in
                     uu____14201.FStar_Syntax_Syntax.v in
                   let uu____14204 =
                     let uu____14205 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14205 in
                   if uu____14204
                   then
                     let val_decl =
                       let uu___151_14220 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14220.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14220.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_14220.FStar_Syntax_Syntax.sigattrs)
                       } in
                     let uu____14224 = encode_sigelt' env1 val_decl in
                     match uu____14224 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____14186 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14241,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14243;
                          FStar_Syntax_Syntax.lbtyp = uu____14244;
                          FStar_Syntax_Syntax.lbeff = uu____14245;
                          FStar_Syntax_Syntax.lbdef = uu____14246;_}::[]),uu____14247)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____14259 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14259 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____14278 =
                   let uu____14280 =
                     let uu____14281 =
                       let uu____14285 =
                         let uu____14286 =
                           let uu____14292 =
                             let uu____14293 =
                               let uu____14296 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14296) in
                             FStar_SMTEncoding_Util.mkEq uu____14293 in
                           ([[b2t_x]], [xx], uu____14292) in
                         FStar_SMTEncoding_Util.mkForall uu____14286 in
                       (uu____14285,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14281 in
                   [uu____14280] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____14278 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14313,uu____14314) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_14320  ->
                  match uu___119_14320 with
                  | FStar_Syntax_Syntax.Discriminator uu____14321 -> true
                  | uu____14322 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14324,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14332 =
                     let uu____14333 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14333.FStar_Ident.idText in
                   uu____14332 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_14336  ->
                     match uu___120_14336 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14337 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14340) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_14350  ->
                  match uu___121_14350 with
                  | FStar_Syntax_Syntax.Projector uu____14351 -> true
                  | uu____14354 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____14357 = try_lookup_free_var env l in
          (match uu____14357 with
           | FStar_Pervasives_Native.Some uu____14361 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___152_14364 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_14364.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_14364.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_14364.FStar_Syntax_Syntax.sigattrs)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____14370) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14380) ->
          let uu____14385 = encode_sigelts env ses in
          (match uu____14385 with
           | (g,env1) ->
               let uu____14395 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_14409  ->
                         match uu___122_14409 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____14410;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____14411;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____14412;_}
                             -> false
                         | uu____14414 -> true)) in
               (match uu____14395 with
                | (g',inversions) ->
                    let uu____14423 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_14435  ->
                              match uu___123_14435 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14436 ->
                                  true
                              | uu____14442 -> false)) in
                    (match uu____14423 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____14453,tps,k,uu____14456,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_14467  ->
                    match uu___124_14467 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14468 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14475 = c in
              match uu____14475 with
              | (name,args,uu____14479,uu____14480,uu____14481) ->
                  let uu____14484 =
                    let uu____14485 =
                      let uu____14491 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14502  ->
                                match uu____14502 with
                                | (uu____14506,sort,uu____14508) -> sort)) in
                      (name, uu____14491, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14485 in
                  [uu____14484]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____14526 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14531 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____14531 FStar_Option.isNone)) in
            if uu____14526
            then []
            else
              (let uu____14548 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14548 with
               | (xxsym,xx) ->
                   let uu____14554 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14583  ->
                             fun l  ->
                               match uu____14583 with
                               | (out,decls) ->
                                   let uu____14595 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14595 with
                                    | (uu____14601,data_t) ->
                                        let uu____14603 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14603 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14632 =
                                                 let uu____14633 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14633.FStar_Syntax_Syntax.n in
                                               match uu____14632 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14641,indices) ->
                                                   indices
                                               | uu____14657 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14674  ->
                                                         match uu____14674
                                                         with
                                                         | (x,uu____14678) ->
                                                             let uu____14679
                                                               =
                                                               let uu____14680
                                                                 =
                                                                 let uu____14684
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14684,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14680 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14679)
                                                    env) in
                                             let uu____14686 =
                                               encode_args indices env1 in
                                             (match uu____14686 with
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
                                                      let uu____14710 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14721
                                                                 =
                                                                 let uu____14724
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14724,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14721)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14710
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14726 =
                                                      let uu____14727 =
                                                        let uu____14730 =
                                                          let uu____14731 =
                                                            let uu____14734 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14734,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14731 in
                                                        (out, uu____14730) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14727 in
                                                    (uu____14726,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14554 with
                    | (data_ax,decls) ->
                        let uu____14742 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14742 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14756 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14756 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14759 =
                                 let uu____14763 =
                                   let uu____14764 =
                                     let uu____14770 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14778 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14770,
                                       uu____14778) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14764 in
                                 let uu____14786 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14763,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____14786) in
                               FStar_SMTEncoding_Util.mkAssume uu____14759 in
                             let pattern_guarded_inversion =
                               let uu____14790 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14790
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14801 =
                                   let uu____14802 =
                                     let uu____14806 =
                                       let uu____14807 =
                                         let uu____14813 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14821 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14813, uu____14821) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14807 in
                                     let uu____14829 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14806,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____14829) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14802 in
                                 [uu____14801]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14832 =
            let uu____14840 =
              let uu____14841 = FStar_Syntax_Subst.compress k in
              uu____14841.FStar_Syntax_Syntax.n in
            match uu____14840 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14870 -> (tps, k) in
          (match uu____14832 with
           | (formals,res) ->
               let uu____14885 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14885 with
                | (formals1,res1) ->
                    let uu____14892 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____14892 with
                     | (vars,guards,env',binder_decls,uu____14907) ->
                         let uu____14914 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14914 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14927 =
                                  let uu____14931 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14931) in
                                FStar_SMTEncoding_Util.mkApp uu____14927 in
                              let uu____14936 =
                                let tname_decl =
                                  let uu____14942 =
                                    let uu____14943 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14961  ->
                                              match uu____14961 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14969 = varops.next_id () in
                                    (tname, uu____14943,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14969, false) in
                                  constructor_or_logic_type_decl uu____14942 in
                                let uu____14974 =
                                  match vars with
                                  | [] ->
                                      let uu____14981 =
                                        let uu____14982 =
                                          let uu____14984 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____14984 in
                                        push_free_var env1 t tname
                                          uu____14982 in
                                      ([], uu____14981)
                                  | uu____14988 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____14994 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14994 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____15003 =
                                          let uu____15007 =
                                            let uu____15008 =
                                              let uu____15016 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____15016) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____15008 in
                                          (uu____15007,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____15003 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14974 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14936 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____15039 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____15039 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____15056 =
                                               let uu____15057 =
                                                 let uu____15061 =
                                                   let uu____15062 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____15062 in
                                                 (uu____15061,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15057 in
                                             [uu____15056]
                                           else [] in
                                         let uu____15065 =
                                           let uu____15067 =
                                             let uu____15069 =
                                               let uu____15070 =
                                                 let uu____15074 =
                                                   let uu____15075 =
                                                     let uu____15081 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____15081) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____15075 in
                                                 (uu____15074,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15070 in
                                             [uu____15069] in
                                           FStar_List.append karr uu____15067 in
                                         FStar_List.append decls1 uu____15065 in
                                   let aux =
                                     let uu____15090 =
                                       let uu____15092 =
                                         inversion_axioms tapp vars in
                                       let uu____15094 =
                                         let uu____15096 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____15096] in
                                       FStar_List.append uu____15092
                                         uu____15094 in
                                     FStar_List.append kindingAx uu____15090 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15101,uu____15102,uu____15103,uu____15104,uu____15105)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15110,t,uu____15112,n_tps,uu____15114) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____15119 = new_term_constant_and_tok_from_lid env d in
          (match uu____15119 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____15130 = FStar_Syntax_Util.arrow_formals t in
               (match uu____15130 with
                | (formals,t_res) ->
                    let uu____15152 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____15152 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____15161 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____15161 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____15203 =
                                            mk_term_projector_name d x in
                                          (uu____15203,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15205 =
                                  let uu____15215 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15215, true) in
                                FStar_All.pipe_right uu____15205
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
                              let uu____15237 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____15237 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15245::uu____15246 ->
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
                                         let uu____15271 =
                                           let uu____15277 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15277) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15271
                                     | uu____15290 -> tok_typing in
                                   let uu____15295 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____15295 with
                                    | (vars',guards',env'',decls_formals,uu____15310)
                                        ->
                                        let uu____15317 =
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
                                        (match uu____15317 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15336 ->
                                                   let uu____15340 =
                                                     let uu____15341 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15341 in
                                                   [uu____15340] in
                                             let encode_elim uu____15348 =
                                               let uu____15349 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____15349 with
                                               | (head1,args) ->
                                                   let uu____15378 =
                                                     let uu____15379 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____15379.FStar_Syntax_Syntax.n in
                                                   (match uu____15378 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____15386;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____15387;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____15388;_},uu____15389)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15395 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15395
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
                                                                 | uu____15424
                                                                    ->
                                                                    let uu____15425
                                                                    =
                                                                    let uu____15426
                                                                    =
                                                                    let uu____15429
                                                                    =
                                                                    let uu____15430
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15430 in
                                                                    (uu____15429,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____15426 in
                                                                    raise
                                                                    uu____15425 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15441
                                                                    =
                                                                    let uu____15442
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15442 in
                                                                    if
                                                                    uu____15441
                                                                    then
                                                                    let uu____15449
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15449]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15451
                                                               =
                                                               let uu____15458
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15491
                                                                     ->
                                                                    fun
                                                                    uu____15492
                                                                     ->
                                                                    match 
                                                                    (uu____15491,
                                                                    uu____15492)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15543
                                                                    =
                                                                    let uu____15547
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15547 in
                                                                    (match uu____15543
                                                                    with
                                                                    | 
                                                                    (uu____15554,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15560
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15560
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15562
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15562
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
                                                                 uu____15458 in
                                                             (match uu____15451
                                                              with
                                                              | (uu____15570,arg_vars,elim_eqns_or_guards,uu____15573)
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
                                                                    let uu____15592
                                                                    =
                                                                    let uu____15596
                                                                    =
                                                                    let uu____15597
                                                                    =
                                                                    let uu____15603
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15609
                                                                    =
                                                                    let uu____15610
                                                                    =
                                                                    let uu____15613
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15613) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15610 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15603,
                                                                    uu____15609) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15597 in
                                                                    (uu____15596,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15592 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15626
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15626,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15628
                                                                    =
                                                                    let uu____15632
                                                                    =
                                                                    let uu____15633
                                                                    =
                                                                    let uu____15639
                                                                    =
                                                                    let uu____15642
                                                                    =
                                                                    let uu____15644
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15644] in
                                                                    [uu____15642] in
                                                                    let uu____15647
                                                                    =
                                                                    let uu____15648
                                                                    =
                                                                    let uu____15651
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15652
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15651,
                                                                    uu____15652) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15648 in
                                                                    (uu____15639,
                                                                    [x],
                                                                    uu____15647) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15633 in
                                                                    let uu____15662
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15632,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15662) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15628
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15667
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
                                                                    (let uu____15684
                                                                    =
                                                                    let uu____15685
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15685
                                                                    dapp1 in
                                                                    [uu____15684]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15667
                                                                    FStar_List.flatten in
                                                                    let uu____15689
                                                                    =
                                                                    let uu____15693
                                                                    =
                                                                    let uu____15694
                                                                    =
                                                                    let uu____15700
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15706
                                                                    =
                                                                    let uu____15707
                                                                    =
                                                                    let uu____15710
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15710) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15707 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15700,
                                                                    uu____15706) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15694 in
                                                                    (uu____15693,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15689) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15722 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15722
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
                                                                 | uu____15751
                                                                    ->
                                                                    let uu____15752
                                                                    =
                                                                    let uu____15753
                                                                    =
                                                                    let uu____15756
                                                                    =
                                                                    let uu____15757
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____15757 in
                                                                    (uu____15756,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos)) in
                                                                    FStar_Errors.Error
                                                                    uu____15753 in
                                                                    raise
                                                                    uu____15752 in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15768
                                                                    =
                                                                    let uu____15769
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15769 in
                                                                    if
                                                                    uu____15768
                                                                    then
                                                                    let uu____15776
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15776]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15778
                                                               =
                                                               let uu____15785
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15818
                                                                     ->
                                                                    fun
                                                                    uu____15819
                                                                     ->
                                                                    match 
                                                                    (uu____15818,
                                                                    uu____15819)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____15870
                                                                    =
                                                                    let uu____15874
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15874 in
                                                                    (match uu____15870
                                                                    with
                                                                    | 
                                                                    (uu____15881,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15887
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv in
                                                                    uu____15887
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15889
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15889
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
                                                                 uu____15785 in
                                                             (match uu____15778
                                                              with
                                                              | (uu____15897,arg_vars,elim_eqns_or_guards,uu____15900)
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
                                                                    let uu____15919
                                                                    =
                                                                    let uu____15923
                                                                    =
                                                                    let uu____15924
                                                                    =
                                                                    let uu____15930
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15936
                                                                    =
                                                                    let uu____15937
                                                                    =
                                                                    let uu____15940
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15940) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15937 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15930,
                                                                    uu____15936) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15924 in
                                                                    (uu____15923,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15919 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15953
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15953,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15955
                                                                    =
                                                                    let uu____15959
                                                                    =
                                                                    let uu____15960
                                                                    =
                                                                    let uu____15966
                                                                    =
                                                                    let uu____15969
                                                                    =
                                                                    let uu____15971
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15971] in
                                                                    [uu____15969] in
                                                                    let uu____15974
                                                                    =
                                                                    let uu____15975
                                                                    =
                                                                    let uu____15978
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15979
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15978,
                                                                    uu____15979) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15975 in
                                                                    (uu____15966,
                                                                    [x],
                                                                    uu____15974) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15960 in
                                                                    let uu____15989
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15959,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15989) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15955
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15994
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
                                                                    (let uu____16011
                                                                    =
                                                                    let uu____16012
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____16012
                                                                    dapp1 in
                                                                    [uu____16011]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15994
                                                                    FStar_List.flatten in
                                                                    let uu____16016
                                                                    =
                                                                    let uu____16020
                                                                    =
                                                                    let uu____16021
                                                                    =
                                                                    let uu____16027
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16033
                                                                    =
                                                                    let uu____16034
                                                                    =
                                                                    let uu____16037
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16037) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16034 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16027,
                                                                    uu____16033) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16021 in
                                                                    (uu____16020,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16016) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____16047 ->
                                                        ((let uu____16049 =
                                                            let uu____16050 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____16051 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____16050
                                                              uu____16051 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____16049);
                                                         ([], []))) in
                                             let uu____16054 = encode_elim () in
                                             (match uu____16054 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____16066 =
                                                      let uu____16068 =
                                                        let uu____16070 =
                                                          let uu____16072 =
                                                            let uu____16074 =
                                                              let uu____16075
                                                                =
                                                                let uu____16081
                                                                  =
                                                                  let uu____16083
                                                                    =
                                                                    let uu____16084
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16084 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____16083 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____16081) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____16075 in
                                                            [uu____16074] in
                                                          let uu____16087 =
                                                            let uu____16089 =
                                                              let uu____16091
                                                                =
                                                                let uu____16093
                                                                  =
                                                                  let uu____16095
                                                                    =
                                                                    let uu____16097
                                                                    =
                                                                    let uu____16099
                                                                    =
                                                                    let uu____16100
                                                                    =
                                                                    let uu____16104
                                                                    =
                                                                    let uu____16105
                                                                    =
                                                                    let uu____16111
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16111) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16105 in
                                                                    (uu____16104,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16100 in
                                                                    let uu____16118
                                                                    =
                                                                    let uu____16120
                                                                    =
                                                                    let uu____16121
                                                                    =
                                                                    let uu____16125
                                                                    =
                                                                    let uu____16126
                                                                    =
                                                                    let uu____16132
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____16138
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16132,
                                                                    uu____16138) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16126 in
                                                                    (uu____16125,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16121 in
                                                                    [uu____16120] in
                                                                    uu____16099
                                                                    ::
                                                                    uu____16118 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____16097 in
                                                                  FStar_List.append
                                                                    uu____16095
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____16093 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____16091 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____16089 in
                                                          FStar_List.append
                                                            uu____16072
                                                            uu____16087 in
                                                        FStar_List.append
                                                          decls3 uu____16070 in
                                                      FStar_List.append
                                                        decls2 uu____16068 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____16066 in
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
           (fun uu____16166  ->
              fun se  ->
                match uu____16166 with
                | (g,env1) ->
                    let uu____16178 = encode_sigelt env1 se in
                    (match uu____16178 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16216 =
        match uu____16216 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____16234 ->
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
                 ((let uu____16239 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____16239
                   then
                     let uu____16240 = FStar_Syntax_Print.bv_to_string x in
                     let uu____16241 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____16242 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16240 uu____16241 uu____16242
                   else ());
                  (let uu____16244 = encode_term t1 env1 in
                   match uu____16244 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____16254 =
                         let uu____16258 =
                           let uu____16259 =
                             let uu____16260 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____16260
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____16259 in
                         new_term_constant_from_string env1 x uu____16258 in
                       (match uu____16254 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____16271 = FStar_Options.log_queries () in
                              if uu____16271
                              then
                                let uu____16273 =
                                  let uu____16274 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____16275 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____16276 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16274 uu____16275 uu____16276 in
                                FStar_Pervasives_Native.Some uu____16273
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____16287,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____16296 = encode_free_var env1 fv t t_norm [] in
                 (match uu____16296 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____16309,se,uu____16311) ->
                 let uu____16314 = encode_sigelt env1 se in
                 (match uu____16314 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16324,se) ->
                 let uu____16328 = encode_sigelt env1 se in
                 (match uu____16328 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16338 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16338 with | (uu____16350,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____16402  ->
            match uu____16402 with
            | (l,uu____16409,uu____16410) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____16437  ->
            match uu____16437 with
            | (l,uu____16445,uu____16446) ->
                let uu____16451 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                    (FStar_Pervasives_Native.fst l) in
                let uu____16452 =
                  let uu____16454 =
                    let uu____16455 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____16455 in
                  [uu____16454] in
                uu____16451 :: uu____16452)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____16467 =
      let uu____16469 =
        let uu____16470 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____16472 =
          let uu____16473 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____16473 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____16470;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____16472
        } in
      [uu____16469] in
    FStar_ST.write last_env uu____16467
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____16485 = FStar_ST.read last_env in
      match uu____16485 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16491 ->
          let uu___153_16493 = e in
          let uu____16494 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_16493.bindings);
            depth = (uu___153_16493.depth);
            tcenv;
            warn = (uu___153_16493.warn);
            cache = (uu___153_16493.cache);
            nolabels = (uu___153_16493.nolabels);
            use_zfuel_name = (uu___153_16493.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_16493.encode_non_total_function_typ);
            current_module_name = uu____16494
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____16499 = FStar_ST.read last_env in
    match uu____16499 with
    | [] -> failwith "Empty env stack"
    | uu____16504::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____16513  ->
    let uu____16514 = FStar_ST.read last_env in
    match uu____16514 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_16525 = hd1 in
          {
            bindings = (uu___154_16525.bindings);
            depth = (uu___154_16525.depth);
            tcenv = (uu___154_16525.tcenv);
            warn = (uu___154_16525.warn);
            cache = refs;
            nolabels = (uu___154_16525.nolabels);
            use_zfuel_name = (uu___154_16525.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_16525.encode_non_total_function_typ);
            current_module_name = (uu___154_16525.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____16532  ->
    let uu____16533 = FStar_ST.read last_env in
    match uu____16533 with
    | [] -> failwith "Popping an empty stack"
    | uu____16538::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____16547  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____16551  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____16555  ->
    let uu____16556 = FStar_ST.read last_env in
    match uu____16556 with
    | hd1::uu____16562::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____16568 -> failwith "Impossible"
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
        | (uu____16627::uu____16628,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16634 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16634.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16634.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16634.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16635 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____16648 =
        let uu____16650 =
          let uu____16651 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____16651 in
        let uu____16652 = open_fact_db_tags env in uu____16650 :: uu____16652 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16648
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
      let uu____16669 = encode_sigelt env se in
      match uu____16669 with
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
        let uu____16696 = FStar_Options.log_queries () in
        if uu____16696
        then
          let uu____16698 =
            let uu____16699 =
              let uu____16700 =
                let uu____16701 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16701 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____16700 in
            FStar_SMTEncoding_Term.Caption uu____16699 in
          uu____16698 :: decls
        else decls in
      let env =
        let uu____16708 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16708 tcenv in
      let uu____16709 = encode_top_level_facts env se in
      match uu____16709 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16718 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____16718))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____16731 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16731
       then
         let uu____16732 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16732
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16762  ->
                 fun se  ->
                   match uu____16762 with
                   | (g,env2) ->
                       let uu____16774 = encode_top_level_facts env2 se in
                       (match uu____16774 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16787 =
         encode_signature
           (let uu___156_16793 = env in
            {
              bindings = (uu___156_16793.bindings);
              depth = (uu___156_16793.depth);
              tcenv = (uu___156_16793.tcenv);
              warn = false;
              cache = (uu___156_16793.cache);
              nolabels = (uu___156_16793.nolabels);
              use_zfuel_name = (uu___156_16793.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16793.encode_non_total_function_typ);
              current_module_name = (uu___156_16793.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16787 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16805 = FStar_Options.log_queries () in
             if uu____16805
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_16812 = env1 in
               {
                 bindings = (uu___157_16812.bindings);
                 depth = (uu___157_16812.depth);
                 tcenv = (uu___157_16812.tcenv);
                 warn = true;
                 cache = (uu___157_16812.cache);
                 nolabels = (uu___157_16812.nolabels);
                 use_zfuel_name = (uu___157_16812.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16812.encode_non_total_function_typ);
                 current_module_name = (uu___157_16812.current_module_name)
               });
            (let uu____16814 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16814
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
        (let uu____16852 =
           let uu____16853 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16853.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16852);
        (let env =
           let uu____16855 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16855 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16864 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16885 = aux rest in
                 (match uu____16885 with
                  | (out,rest1) ->
                      let t =
                        let uu____16903 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16903 with
                        | FStar_Pervasives_Native.Some uu____16907 ->
                            let uu____16908 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16908
                              x.FStar_Syntax_Syntax.sort
                        | uu____16909 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16912 =
                        let uu____16914 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16917 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16917.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16917.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16914 :: out in
                      (uu____16912, rest1))
             | uu____16920 -> ([], bindings1) in
           let uu____16924 = aux bindings in
           match uu____16924 with
           | (closing,bindings1) ->
               let uu____16938 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16938, bindings1) in
         match uu____16864 with
         | (q1,bindings1) ->
             let uu____16951 =
               let uu____16954 =
                 FStar_List.filter
                   (fun uu___125_16958  ->
                      match uu___125_16958 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16959 ->
                          false
                      | uu____16963 -> true) bindings1 in
               encode_env_bindings env uu____16954 in
             (match uu____16951 with
              | (env_decls,env1) ->
                  ((let uu____16974 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16974
                    then
                      let uu____16975 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16975
                    else ());
                   (let uu____16977 = encode_formula q1 env1 in
                    match uu____16977 with
                    | (phi,qdecls) ->
                        let uu____16989 =
                          let uu____16992 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16992 phi in
                        (match uu____16989 with
                         | (labels,phi1) ->
                             let uu____17002 = encode_labels labels in
                             (match uu____17002 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____17023 =
                                      let uu____17027 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____17028 =
                                        varops.mk_unique "@query" in
                                      (uu____17027,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____17028) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____17023 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____17043 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____17043 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____17045 = encode_formula q env in
       match uu____17045 with
       | (f,uu____17049) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____17051) -> true
             | uu____17054 -> false)))