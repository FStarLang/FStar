open Prims
let add_fuel x tl1 =
  let uu____19 = FStar_Options.unthrottle_inductives () in
  if uu____19 then tl1 else x :: tl1
let withenv c uu____47 = match uu____47 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___101_86  ->
       match uu___101_86 with
       | (FStar_Util.Inl uu____91,uu____92) -> false
       | uu____95 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____129 =
        let uu____132 =
          let uu____133 =
            let uu____136 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____136 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____133 in
        FStar_Util.Inl uu____132 in
      Some uu____129
  | uu____141 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___125_158 = a in
        let uu____159 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____159;
          FStar_Syntax_Syntax.index =
            (uu___125_158.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___125_158.FStar_Syntax_Syntax.sort)
        } in
      let uu____160 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____160
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____176 =
          let uu____177 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____177 in
        let uu____178 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____178 with
        | (uu____181,t) ->
            let uu____183 =
              let uu____184 = FStar_Syntax_Subst.compress t in
              uu____184.FStar_Syntax_Syntax.n in
            (match uu____183 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____199 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____199 with
                  | (binders,uu____203) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (fst b)))
             | uu____216 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____225 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____225
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____234 =
        let uu____237 = mk_term_projector_name lid a in
        (uu____237,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____234
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____246 =
        let uu____249 = mk_term_projector_name_by_pos lid i in
        (uu____249,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____246
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
  let new_scope uu____863 =
    let uu____864 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____866 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____864, uu____866) in
  let scopes =
    let uu____877 = let uu____883 = new_scope () in [uu____883] in
    FStar_Util.mk_ref uu____877 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____908 =
        let uu____910 = FStar_ST.read scopes in
        FStar_Util.find_map uu____910
          (fun uu____927  ->
             match uu____927 with
             | (names1,uu____934) -> FStar_Util.smap_try_find names1 y1) in
      match uu____908 with
      | None  -> y1
      | Some uu____939 ->
          (FStar_Util.incr ctr;
           (let uu____944 =
              let uu____945 =
                let uu____946 = FStar_ST.read ctr in
                Prims.string_of_int uu____946 in
              Prims.strcat "__" uu____945 in
            Prims.strcat y1 uu____944)) in
    let top_scope =
      let uu____951 =
        let uu____956 = FStar_ST.read scopes in FStar_List.hd uu____956 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____951 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____995 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____1006 =
      let uu____1007 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____1007 in
    FStar_Util.format2 "%s_%s" pfx uu____1006 in
  let string_const s =
    let uu____1012 =
      let uu____1014 = FStar_ST.read scopes in
      FStar_Util.find_map uu____1014
        (fun uu____1031  ->
           match uu____1031 with
           | (uu____1037,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____1012 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____1046 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1046 in
        let top_scope =
          let uu____1049 =
            let uu____1054 = FStar_ST.read scopes in FStar_List.hd uu____1054 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____1049 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1082 =
    let uu____1083 =
      let uu____1089 = new_scope () in
      let uu____1094 = FStar_ST.read scopes in uu____1089 :: uu____1094 in
    FStar_ST.write scopes uu____1083 in
  let pop1 uu____1121 =
    let uu____1122 =
      let uu____1128 = FStar_ST.read scopes in FStar_List.tl uu____1128 in
    FStar_ST.write scopes uu____1122 in
  let mark1 uu____1155 = push1 () in
  let reset_mark1 uu____1159 = pop1 () in
  let commit_mark1 uu____1163 =
    let uu____1164 = FStar_ST.read scopes in
    match uu____1164 with
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
    | uu____1224 -> failwith "Impossible" in
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
    let uu___126_1234 = x in
    let uu____1235 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1235;
      FStar_Syntax_Syntax.index = (uu___126_1234.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___126_1234.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1259 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1285 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term option*
      FStar_SMTEncoding_Term.term option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, None)
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
         (fun uu___102_1609  ->
            match uu___102_1609 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1612 -> [])) in
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
    let uu____1622 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1626  ->
              match uu___103_1626 with
              | Binding_var (x,uu____1628) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1630,uu____1631,uu____1632) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1622 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1670 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1670
      then
        let uu____1672 = FStar_Syntax_Print.term_to_string t in
        Some uu____1672
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1685 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1685)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___127_1699 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___127_1699.tcenv);
           warn = (uu___127_1699.warn);
           cache = (uu___127_1699.cache);
           nolabels = (uu___127_1699.nolabels);
           use_zfuel_name = (uu___127_1699.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___127_1699.encode_non_total_function_typ);
           current_module_name = (uu___127_1699.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___128_1714 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___128_1714.depth);
           tcenv = (uu___128_1714.tcenv);
           warn = (uu___128_1714.warn);
           cache = (uu___128_1714.cache);
           nolabels = (uu___128_1714.nolabels);
           use_zfuel_name = (uu___128_1714.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1714.encode_non_total_function_typ);
           current_module_name = (uu___128_1714.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___129_1733 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___129_1733.depth);
             tcenv = (uu___129_1733.tcenv);
             warn = (uu___129_1733.warn);
             cache = (uu___129_1733.cache);
             nolabels = (uu___129_1733.nolabels);
             use_zfuel_name = (uu___129_1733.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___129_1733.encode_non_total_function_typ);
             current_module_name = (uu___129_1733.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___130_1746 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___130_1746.depth);
          tcenv = (uu___130_1746.tcenv);
          warn = (uu___130_1746.warn);
          cache = (uu___130_1746.cache);
          nolabels = (uu___130_1746.nolabels);
          use_zfuel_name = (uu___130_1746.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___130_1746.encode_non_total_function_typ);
          current_module_name = (uu___130_1746.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1764  ->
             match uu___104_1764 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1772 -> None) in
      let uu____1775 = aux a in
      match uu____1775 with
      | None  ->
          let a2 = unmangle a in
          let uu____1782 = aux a2 in
          (match uu____1782 with
           | None  ->
               let uu____1788 =
                 let uu____1789 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1790 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1789 uu____1790 in
               failwith uu____1788
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1812 =
        let uu___131_1813 = env in
        let uu____1814 =
          let uu____1816 =
            let uu____1817 =
              let uu____1824 =
                let uu____1826 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1826 in
              (x, fname, uu____1824, None) in
            Binding_fvar uu____1817 in
          uu____1816 :: (env.bindings) in
        {
          bindings = uu____1814;
          depth = (uu___131_1813.depth);
          tcenv = (uu___131_1813.tcenv);
          warn = (uu___131_1813.warn);
          cache = (uu___131_1813.cache);
          nolabels = (uu___131_1813.nolabels);
          use_zfuel_name = (uu___131_1813.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1813.encode_non_total_function_typ);
          current_module_name = (uu___131_1813.current_module_name)
        } in
      (fname, ftok, uu____1812)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1850  ->
           match uu___105_1850 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1872 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1886 =
        lookup_binding env
          (fun uu___106_1888  ->
             match uu___106_1888 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1898 -> None) in
      FStar_All.pipe_right uu____1886 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1913 = try_lookup_lid env a in
      match uu____1913 with
      | None  ->
          let uu____1930 =
            let uu____1931 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1931 in
          failwith uu____1930
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___132_1966 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___132_1966.depth);
            tcenv = (uu___132_1966.tcenv);
            warn = (uu___132_1966.warn);
            cache = (uu___132_1966.cache);
            nolabels = (uu___132_1966.nolabels);
            use_zfuel_name = (uu___132_1966.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_1966.encode_non_total_function_typ);
            current_module_name = (uu___132_1966.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1981 = lookup_lid env x in
        match uu____1981 with
        | (t1,t2,uu____1989) ->
            let t3 =
              let uu____1995 =
                let uu____1999 =
                  let uu____2001 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____2001] in
                (f, uu____1999) in
              FStar_SMTEncoding_Util.mkApp uu____1995 in
            let uu___133_2004 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___133_2004.depth);
              tcenv = (uu___133_2004.tcenv);
              warn = (uu___133_2004.warn);
              cache = (uu___133_2004.cache);
              nolabels = (uu___133_2004.nolabels);
              use_zfuel_name = (uu___133_2004.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___133_2004.encode_non_total_function_typ);
              current_module_name = (uu___133_2004.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____2016 = try_lookup_lid env l in
      match uu____2016 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____2043 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2048,fuel::[]) ->
                         let uu____2051 =
                           let uu____2052 =
                             let uu____2053 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____2053
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____2052 "fuel" in
                         if uu____2051
                         then
                           let uu____2055 =
                             let uu____2056 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2056
                               fuel in
                           FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                             uu____2055
                         else Some t
                     | uu____2059 -> Some t)
                | uu____2060 -> None))
let lookup_free_var env a =
  let uu____2081 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____2081 with
  | Some t -> t
  | None  ->
      let uu____2084 =
        let uu____2085 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____2085 in
      failwith uu____2084
let lookup_free_var_name env a =
  let uu____2105 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____2105 with | (x,uu____2112,uu____2113) -> x
let lookup_free_var_sym env a =
  let uu____2140 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____2140 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____2161;
             FStar_SMTEncoding_Term.rng = uu____2162;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____2170 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____2184 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_2195  ->
           match uu___107_2195 with
           | Binding_fvar (uu____2197,nm',tok,uu____2200) when nm = nm' ->
               tok
           | uu____2205 -> None)
let mkForall_fuel' n1 uu____2225 =
  match uu____2225 with
  | (pats,vars,body) ->
      let fallback uu____2241 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____2244 = FStar_Options.unthrottle_inductives () in
      if uu____2244
      then fallback ()
      else
        (let uu____2246 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____2246 with
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
                       | uu____2265 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____2279 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____2279
                     | uu____2281 ->
                         let uu____2282 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____2282 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____2285 -> body in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____2314 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2322 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2327 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2328 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2337 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2352 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2354 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2354 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2368;
             FStar_Syntax_Syntax.pos = uu____2369;
             FStar_Syntax_Syntax.vars = uu____2370;_},uu____2371)
          ->
          let uu____2386 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2386 FStar_Option.isNone
      | uu____2399 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2408 =
        let uu____2409 = FStar_Syntax_Util.un_uinst t in
        uu____2409.FStar_Syntax_Syntax.n in
      match uu____2408 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2412,uu____2413,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_2442  ->
                  match uu___108_2442 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2443 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2444,uu____2445,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2472 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2472 FStar_Option.isSome
      | uu____2485 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2494 = head_normal env t in
      if uu____2494
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
    let uu____2508 =
      let uu____2509 = FStar_Syntax_Syntax.null_binder t in [uu____2509] in
    let uu____2510 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____2508 uu____2510 None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____2539 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2539
                | s ->
                    let uu____2542 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2542) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_2557  ->
    match uu___109_2557 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2558 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term option
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
                       FStar_SMTEncoding_Term.freevars = uu____2589;
                       FStar_SMTEncoding_Term.rng = uu____2590;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2604) ->
              let uu____2609 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2623 -> false) args (FStar_List.rev xs)) in
              if uu____2609 then tok_of_name env f else None
          | (uu____2626,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2629 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2631 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2631)) in
              if uu____2629 then Some t else None
          | uu____2634 -> None in
        check_partial_applications body (FStar_List.rev vars)
type label = (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t);
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list;}
let __proj__Mkpattern__item__pat_vars:
  pattern -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
let __proj__Mkpattern__item__pat_term:
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
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
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list
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
    | uu____2801 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2805  ->
    match uu___110_2805 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2807 =
          let uu____2811 =
            let uu____2813 =
              let uu____2814 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2814 in
            [uu____2813] in
          ("FStar.Char.Char", uu____2811) in
        FStar_SMTEncoding_Util.mkApp uu____2807
    | FStar_Const.Const_int (i,None ) ->
        let uu____2822 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2822
    | FStar_Const.Const_int (i,Some uu____2824) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2833) ->
        let uu____2836 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2836
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2840 =
          let uu____2841 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2841 in
        failwith uu____2840
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2862 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2870 ->
            let uu____2875 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2875
        | uu____2876 ->
            if norm1
            then let uu____2877 = whnf env t1 in aux false uu____2877
            else
              (let uu____2879 =
                 let uu____2880 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2881 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2880 uu____2881 in
               failwith uu____2879) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2903 ->
        let uu____2904 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2904)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2936::uu____2937::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2940::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2942 -> false
let rec encode_binders:
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____3080 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____3080
         then
           let uu____3081 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____3081
         else ());
        (let uu____3083 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3119  ->
                   fun b  ->
                     match uu____3119 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3162 =
                           let x = unmangle (fst b) in
                           let uu____3171 = gen_term_var env1 x in
                           match uu____3171 with
                           | (xxsym,xx,env') ->
                               let uu____3185 =
                                 let uu____3188 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3188 env1 xx in
                               (match uu____3185 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____3162 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____3083 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____3276 = encode_term t env in
          match uu____3276 with
          | (t1,decls) ->
              let uu____3283 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3283, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____3291 = encode_term t env in
          match uu____3291 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____3300 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3300, decls)
               | Some f ->
                   let uu____3302 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3302, decls))
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____3308 = encode_args args_e env in
        match uu____3308 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3320 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3327 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3327 in
            let binary arg_tms1 =
              let uu____3336 =
                let uu____3337 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3337 in
              let uu____3338 =
                let uu____3339 =
                  let uu____3340 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3340 in
                FStar_SMTEncoding_Term.unboxInt uu____3339 in
              (uu____3336, uu____3338) in
            let mk_default uu____3345 =
              let uu____3346 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3346 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3391 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3391
              then
                let uu____3392 = let uu____3393 = mk_args ts in op uu____3393 in
                FStar_All.pipe_right uu____3392 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3416 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3416
              then
                let uu____3417 = binary ts in
                match uu____3417 with
                | (t1,t2) ->
                    let uu____3422 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3422
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3425 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3425
                 then
                   let uu____3426 = op (binary ts) in
                   FStar_All.pipe_right uu____3426
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Syntax_Const.op_Addition, add1);
              (FStar_Syntax_Const.op_Subtraction, sub1);
              (FStar_Syntax_Const.op_Multiply, mul1);
              (FStar_Syntax_Const.op_Division, div1);
              (FStar_Syntax_Const.op_Modulus, modulus);
              (FStar_Syntax_Const.op_Minus, minus)] in
            let uu____3516 =
              let uu____3522 =
                FStar_List.tryFind
                  (fun uu____3534  ->
                     match uu____3534 with
                     | (l,uu____3541) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3522 FStar_Util.must in
            (match uu____3516 with
             | (uu____3566,op) ->
                 let uu____3574 = op arg_tms in (uu____3574, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____3581 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3581
       then
         let uu____3582 = FStar_Syntax_Print.tag_of_term t in
         let uu____3583 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3584 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3582 uu____3583
           uu____3584
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3588 ->
           let uu____3609 =
             let uu____3610 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3611 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3612 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3613 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3610
               uu____3611 uu____3612 uu____3613 in
           failwith uu____3609
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3616 =
             let uu____3617 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3618 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3619 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3620 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3617
               uu____3618 uu____3619 uu____3620 in
           failwith uu____3616
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3624 =
             let uu____3625 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3625 in
           failwith uu____3624
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3630) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3660) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3669 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3669, [])
       | FStar_Syntax_Syntax.Tm_type uu____3675 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3678) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3684 = encode_const c in (uu____3684, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3699 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3699 with
            | (binders1,res) ->
                let uu____3706 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3706
                then
                  let uu____3709 = encode_binders None binders1 env in
                  (match uu____3709 with
                   | (vars,guards,env',decls,uu____3724) ->
                       let fsym =
                         let uu____3734 = varops.fresh "f" in
                         (uu____3734, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3737 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___134_3741 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___134_3741.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___134_3741.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___134_3741.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___134_3741.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___134_3741.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___134_3741.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___134_3741.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___134_3741.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___134_3741.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___134_3741.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___134_3741.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___134_3741.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___134_3741.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___134_3741.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___134_3741.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___134_3741.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___134_3741.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___134_3741.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___134_3741.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___134_3741.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___134_3741.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___134_3741.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___134_3741.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___134_3741.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___134_3741.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___134_3741.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____3737 with
                        | (pre_opt,res_t) ->
                            let uu____3748 =
                              encode_term_pred None res_t env' app in
                            (match uu____3748 with
                             | (res_pred,decls') ->
                                 let uu____3755 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3762 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3762, [])
                                   | Some pre ->
                                       let uu____3765 =
                                         encode_formula pre env' in
                                       (match uu____3765 with
                                        | (guard,decls0) ->
                                            let uu____3773 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3773, decls0)) in
                                 (match uu____3755 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3781 =
                                          let uu____3787 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3787) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3781 in
                                      let cvars =
                                        let uu____3797 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3797
                                          (FStar_List.filter
                                             (fun uu____3803  ->
                                                match uu____3803 with
                                                | (x,uu____3807) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3818 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3818 with
                                       | Some cache_entry ->
                                           let uu____3823 =
                                             let uu____3824 =
                                               let uu____3828 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3828) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3824 in
                                           (uu____3823,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3839 =
                                               let uu____3840 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3840 in
                                             varops.mk_unique uu____3839 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3847 =
                                               FStar_Options.log_queries () in
                                             if uu____3847
                                             then
                                               let uu____3849 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3849
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3855 =
                                               let uu____3859 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3859) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3855 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3867 =
                                               let uu____3871 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3871, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3867 in
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
                                             let uu____3884 =
                                               let uu____3888 =
                                                 let uu____3889 =
                                                   let uu____3895 =
                                                     let uu____3896 =
                                                       let uu____3899 =
                                                         let uu____3900 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3900 in
                                                       (f_has_t, uu____3899) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3896 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3895) in
                                                 mkForall_fuel uu____3889 in
                                               (uu____3888,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3884 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3913 =
                                               let uu____3917 =
                                                 let uu____3918 =
                                                   let uu____3924 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3924) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3918 in
                                               (uu____3917, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3913 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3938 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3938);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____3949 =
                       let uu____3953 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3953, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3949 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3962 =
                       let uu____3966 =
                         let uu____3967 =
                           let uu____3973 =
                             let uu____3974 =
                               let uu____3977 =
                                 let uu____3978 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3978 in
                               (f_has_t, uu____3977) in
                             FStar_SMTEncoding_Util.mkImp uu____3974 in
                           ([[f_has_t]], [fsym], uu____3973) in
                         mkForall_fuel uu____3967 in
                       (uu____3966, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3962 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3992 ->
           let uu____3997 =
             let uu____4000 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____4000 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____4005;
                 FStar_Syntax_Syntax.pos = uu____4006;
                 FStar_Syntax_Syntax.vars = uu____4007;_} ->
                 let uu____4014 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____4014 with
                  | (b,f1) ->
                      let uu____4028 =
                        let uu____4029 = FStar_List.hd b in fst uu____4029 in
                      (uu____4028, f1))
             | uu____4034 -> failwith "impossible" in
           (match uu____3997 with
            | (x,f) ->
                let uu____4041 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____4041 with
                 | (base_t,decls) ->
                     let uu____4048 = gen_term_var env x in
                     (match uu____4048 with
                      | (x1,xtm,env') ->
                          let uu____4057 = encode_formula f env' in
                          (match uu____4057 with
                           | (refinement,decls') ->
                               let uu____4064 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____4064 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____4075 =
                                        let uu____4077 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____4081 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____4077
                                          uu____4081 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4075 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4097  ->
                                              match uu____4097 with
                                              | (y,uu____4101) ->
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
                                    let uu____4120 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____4120 with
                                     | Some cache_entry ->
                                         let uu____4125 =
                                           let uu____4126 =
                                             let uu____4130 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4130) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4126 in
                                         (uu____4125,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____4142 =
                                             let uu____4143 =
                                               let uu____4144 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4144 in
                                             Prims.strcat module_name
                                               uu____4143 in
                                           varops.mk_unique uu____4142 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____4153 =
                                             let uu____4157 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____4157) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4153 in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1 in
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
                                           let uu____4168 =
                                             let uu____4172 =
                                               let uu____4173 =
                                                 let uu____4179 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4179) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4173 in
                                             (uu____4172,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4168 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4194 =
                                             let uu____4198 =
                                               let uu____4199 =
                                                 let uu____4205 =
                                                   let uu____4206 =
                                                     let uu____4209 =
                                                       let uu____4210 =
                                                         let uu____4216 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4216) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4210 in
                                                     (uu____4209, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4206 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4205) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4199 in
                                             (uu____4198,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4194 in
                                         let t_kinding =
                                           let uu____4236 =
                                             let uu____4240 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4240,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4236 in
                                         let t_interp =
                                           let uu____4250 =
                                             let uu____4254 =
                                               let uu____4255 =
                                                 let uu____4261 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4261) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4255 in
                                             let uu____4273 =
                                               let uu____4275 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____4275 in
                                             (uu____4254, uu____4273,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4250 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4280 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4280);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4297 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4297 in
           let uu____4298 = encode_term_pred None k env ttm in
           (match uu____4298 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4306 =
                    let uu____4310 =
                      let uu____4311 =
                        let uu____4312 =
                          let uu____4313 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4313 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4312 in
                      varops.mk_unique uu____4311 in
                    (t_has_k, (Some "Uvar typing"), uu____4310) in
                  FStar_SMTEncoding_Util.mkAssume uu____4306 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4316 ->
           let uu____4326 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4326 with
            | (head1,args_e) ->
                let uu____4354 =
                  let uu____4362 =
                    let uu____4363 = FStar_Syntax_Subst.compress head1 in
                    uu____4363.FStar_Syntax_Syntax.n in
                  (uu____4362, args_e) in
                (match uu____4354 with
                 | uu____4373 when head_redex env head1 ->
                     let uu____4381 = whnf env t in
                     encode_term uu____4381 env
                 | uu____4382 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____4395;
                       FStar_Syntax_Syntax.pos = uu____4396;
                       FStar_Syntax_Syntax.vars = uu____4397;_},uu____4398),uu____4399::
                    (v1,uu____4401)::(v2,uu____4403)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4441 = encode_term v1 env in
                     (match uu____4441 with
                      | (v11,decls1) ->
                          let uu____4448 = encode_term v2 env in
                          (match uu____4448 with
                           | (v21,decls2) ->
                               let uu____4455 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4455,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4458::(v1,uu____4460)::(v2,uu____4462)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4496 = encode_term v1 env in
                     (match uu____4496 with
                      | (v11,decls1) ->
                          let uu____4503 = encode_term v2 env in
                          (match uu____4503 with
                           | (v21,decls2) ->
                               let uu____4510 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4510,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4512) ->
                     let e0 =
                       let uu____4524 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____4524 in
                     ((let uu____4530 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____4530
                       then
                         let uu____4531 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4531
                       else ());
                      (let e =
                         let uu____4536 =
                           let uu____4537 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____4538 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4537
                             uu____4538 in
                         uu____4536 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4547),(arg,uu____4549)::[]) -> encode_term arg env
                 | uu____4567 ->
                     let uu____4575 = encode_args args_e env in
                     (match uu____4575 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4608 = encode_term head1 env in
                            match uu____4608 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____4647 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4647 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4691  ->
                                                 fun uu____4692  ->
                                                   match (uu____4691,
                                                           uu____4692)
                                                   with
                                                   | ((bv,uu____4706),
                                                      (a,uu____4708)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4722 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4722
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4727 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____4727 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4737 =
                                                   let uu____4741 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4746 =
                                                     let uu____4747 =
                                                       let uu____4748 =
                                                         let uu____4749 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4749 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4748 in
                                                     varops.mk_unique
                                                       uu____4747 in
                                                   (uu____4741,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4746) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4737 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4766 = lookup_free_var_sym env fv in
                            match uu____4766 with
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
                                   FStar_Syntax_Syntax.tk = uu____4789;
                                   FStar_Syntax_Syntax.pos = uu____4790;
                                   FStar_Syntax_Syntax.vars = uu____4791;_},uu____4792)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4803;
                                   FStar_Syntax_Syntax.pos = uu____4804;
                                   FStar_Syntax_Syntax.vars = uu____4805;_},uu____4806)
                                ->
                                let uu____4811 =
                                  let uu____4812 =
                                    let uu____4815 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4815
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4812
                                    FStar_Pervasives.snd in
                                Some uu____4811
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4835 =
                                  let uu____4836 =
                                    let uu____4839 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4839
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4836
                                    FStar_Pervasives.snd in
                                Some uu____4835
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4858,(FStar_Util.Inl t1,uu____4860),uu____4861)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4899,(FStar_Util.Inr c,uu____4901),uu____4902)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4940 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4960 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4960 in
                               let uu____4961 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4961 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4971;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4972;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4973;_},uu____4974)
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
                                     | uu____5006 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____5056 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____5056 with
            | (bs1,body1,opening) ->
                let fallback uu____5071 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____5076 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____5076, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____5087 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____5087
                  | FStar_Util.Inr (eff,uu____5089) ->
                      let uu____5095 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____5095 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____5140 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___135_5141 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___135_5141.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___135_5141.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___135_5141.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___135_5141.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___135_5141.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___135_5141.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___135_5141.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___135_5141.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___135_5141.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___135_5141.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___135_5141.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___135_5141.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___135_5141.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___135_5141.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___135_5141.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___135_5141.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___135_5141.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___135_5141.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___135_5141.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___135_5141.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___135_5141.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___135_5141.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___135_5141.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___135_5141.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___135_5141.FStar_TypeChecker_Env.synth);
                               FStar_TypeChecker_Env.is_native_tactic =
                                 (uu___135_5141.FStar_TypeChecker_Env.is_native_tactic)
                             }) uu____5140 FStar_Syntax_Syntax.U_unknown in
                        let uu____5142 =
                          let uu____5143 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____5143 in
                        FStar_Util.Inl uu____5142
                    | FStar_Util.Inr (eff_name,uu____5150) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____5181 =
                        let uu____5182 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____5182 in
                      FStar_All.pipe_right uu____5181
                        (fun _0_41  -> Some _0_41)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____5194 =
                        let uu____5195 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5195 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____5203 =
                          let uu____5204 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____5204 in
                        FStar_All.pipe_right uu____5203
                          (fun _0_42  -> Some _0_42)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____5208 =
                             let uu____5209 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____5209 in
                           FStar_All.pipe_right uu____5208
                             (fun _0_43  -> Some _0_43))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____5220 =
                         let uu____5221 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5221 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5220);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____5236 =
                       (is_impure lc1) &&
                         (let uu____5237 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____5237) in
                     if uu____5236
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5242 = encode_binders None bs1 env in
                        match uu____5242 with
                        | (vars,guards,envbody,decls,uu____5257) ->
                            let uu____5264 =
                              let uu____5272 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____5272
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____5264 with
                             | (lc2,body2) ->
                                 let uu____5297 = encode_term body2 envbody in
                                 (match uu____5297 with
                                  | (body3,decls') ->
                                      let uu____5304 =
                                        let uu____5309 = codomain_eff lc2 in
                                        match uu____5309 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____5321 =
                                              encode_term tfun env in
                                            (match uu____5321 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____5304 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____5340 =
                                               let uu____5346 =
                                                 let uu____5347 =
                                                   let uu____5350 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____5350, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____5347 in
                                               ([], vars, uu____5346) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____5340 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____5358 =
                                                   let uu____5360 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____5360 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____5358 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____5371 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____5371 with
                                            | Some cache_entry ->
                                                let uu____5376 =
                                                  let uu____5377 =
                                                    let uu____5381 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____5381) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5377 in
                                                (uu____5376,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____5387 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____5387 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____5394 =
                                                         let uu____5395 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____5395 =
                                                           cache_size in
                                                       if uu____5394
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'') in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives.snd
                                                         cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____5406 =
                                                           let uu____5407 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____5407 in
                                                         varops.mk_unique
                                                           uu____5406 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let f =
                                                       let uu____5412 =
                                                         let uu____5416 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____5416) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____5412 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____5428 =
                                                             let uu____5429 =
                                                               let uu____5433
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____5433,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____5429 in
                                                           [uu____5428] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____5441 =
                                                         let uu____5445 =
                                                           let uu____5446 =
                                                             let uu____5452 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____5452) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____5446 in
                                                         (uu____5445,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____5441 in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f]))) in
                                                     ((let uu____5462 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____5462);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5464,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5465;
                          FStar_Syntax_Syntax.lbunivs = uu____5466;
                          FStar_Syntax_Syntax.lbtyp = uu____5467;
                          FStar_Syntax_Syntax.lbeff = uu____5468;
                          FStar_Syntax_Syntax.lbdef = uu____5469;_}::uu____5470),uu____5471)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5489;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5491;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5507 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____5520 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5520, [decl_e])))
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
                 (FStar_SMTEncoding_Term.term*
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____5562 = encode_term e1 env in
              match uu____5562 with
              | (ee1,decls1) ->
                  let uu____5569 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____5569 with
                   | (xs,e21) ->
                       let uu____5583 = FStar_List.hd xs in
                       (match uu____5583 with
                        | (x1,uu____5591) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5593 = encode_body e21 env' in
                            (match uu____5593 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____5615 =
              let uu____5619 =
                let uu____5620 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5620 in
              gen_term_var env uu____5619 in
            match uu____5615 with
            | (scrsym,scr',env1) ->
                let uu____5630 = encode_term e env1 in
                (match uu____5630 with
                 | (scr,decls) ->
                     let uu____5637 =
                       let encode_branch b uu____5653 =
                         match uu____5653 with
                         | (else_case,decls1) ->
                             let uu____5664 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5664 with
                              | (p,w,br) ->
                                  let uu____5685 = encode_pat env1 p in
                                  (match uu____5685 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____5705  ->
                                                   match uu____5705 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____5710 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____5725 =
                                               encode_term w1 env2 in
                                             (match uu____5725 with
                                              | (w2,decls2) ->
                                                  let uu____5733 =
                                                    let uu____5734 =
                                                      let uu____5737 =
                                                        let uu____5738 =
                                                          let uu____5741 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5741) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5738 in
                                                      (guard, uu____5737) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5734 in
                                                  (uu____5733, decls2)) in
                                       (match uu____5710 with
                                        | (guard1,decls2) ->
                                            let uu____5749 =
                                              encode_br br env2 in
                                            (match uu____5749 with
                                             | (br1,decls3) ->
                                                 let uu____5757 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5757,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____5637 with
                      | (match_tm,decls1) ->
                          let uu____5768 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5768, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5790 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5790
       then
         let uu____5791 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5791
       else ());
      (let uu____5793 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5793 with
       | (vars,pat_term) ->
           let uu____5803 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5826  ->
                     fun v1  ->
                       match uu____5826 with
                       | (env1,vars1) ->
                           let uu____5854 = gen_term_var env1 v1 in
                           (match uu____5854 with
                            | (xx,uu____5866,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5803 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5913 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5914 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5915 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5921 =
                        let uu____5924 = encode_const c in
                        (scrutinee, uu____5924) in
                      FStar_SMTEncoding_Util.mkEq uu____5921
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5943 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5943 with
                        | (uu____5947,uu____5948::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5950 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5971  ->
                                  match uu____5971 with
                                  | (arg,uu____5977) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5987 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5987)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____6007) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____6026 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____6041 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____6063  ->
                                  match uu____6063 with
                                  | (arg,uu____6072) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____6082 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____6082)) in
                      FStar_All.pipe_right uu____6041 FStar_List.flatten in
                let pat_term1 uu____6098 = encode_term pat_term env1 in
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
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____6105 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____6120  ->
                fun uu____6121  ->
                  match (uu____6120, uu____6121) with
                  | ((tms,decls),(t,uu____6141)) ->
                      let uu____6152 = encode_term t env in
                      (match uu____6152 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____6105 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____6186 = FStar_Syntax_Util.list_elements e in
        match uu____6186 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____6201 =
          let uu____6211 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____6211 FStar_Syntax_Util.head_and_args in
        match uu____6201 with
        | (head1,args) ->
            let uu____6239 =
              let uu____6247 =
                let uu____6248 = FStar_Syntax_Util.un_uinst head1 in
                uu____6248.FStar_Syntax_Syntax.n in
              (uu____6247, args) in
            (match uu____6239 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6259,uu____6260)::(e,uu____6262)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____6288 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6315 =
            let uu____6325 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6325 FStar_Syntax_Util.head_and_args in
          match uu____6315 with
          | (head1,args) ->
              let uu____6354 =
                let uu____6362 =
                  let uu____6363 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6363.FStar_Syntax_Syntax.n in
                (uu____6362, args) in
              (match uu____6354 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6376)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____6396 -> None) in
        match elts with
        | t1::[] ->
            let uu____6411 = smt_pat_or1 t1 in
            (match uu____6411 with
             | Some e ->
                 let uu____6424 = list_elements1 e in
                 FStar_All.pipe_right uu____6424
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6435 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6435
                           (FStar_List.map one_pat)))
             | uu____6443 ->
                 let uu____6447 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6447])
        | uu____6463 ->
            let uu____6465 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6465] in
      let uu____6481 =
        let uu____6494 =
          let uu____6495 = FStar_Syntax_Subst.compress t in
          uu____6495.FStar_Syntax_Syntax.n in
        match uu____6494 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6522 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6522 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6551;
                        FStar_Syntax_Syntax.effect_name = uu____6552;
                        FStar_Syntax_Syntax.result_typ = uu____6553;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6555)::(post,uu____6557)::(pats,uu____6559)::[];
                        FStar_Syntax_Syntax.flags = uu____6560;_}
                      ->
                      let uu____6592 = lemma_pats pats in
                      (binders1, pre, post, uu____6592)
                  | uu____6605 -> failwith "impos"))
        | uu____6618 -> failwith "Impos" in
      match uu____6481 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6654 = env in
            {
              bindings = (uu___136_6654.bindings);
              depth = (uu___136_6654.depth);
              tcenv = (uu___136_6654.tcenv);
              warn = (uu___136_6654.warn);
              cache = (uu___136_6654.cache);
              nolabels = (uu___136_6654.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6654.encode_non_total_function_typ);
              current_module_name = (uu___136_6654.current_module_name)
            } in
          let uu____6655 = encode_binders None binders env1 in
          (match uu____6655 with
           | (vars,guards,env2,decls,uu____6670) ->
               let uu____6677 =
                 let uu____6684 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6706 =
                             let uu____6711 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6711 FStar_List.unzip in
                           match uu____6706 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6684 FStar_List.unzip in
               (match uu____6677 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6769 = env2 in
                      {
                        bindings = (uu___137_6769.bindings);
                        depth = (uu___137_6769.depth);
                        tcenv = (uu___137_6769.tcenv);
                        warn = (uu___137_6769.warn);
                        cache = (uu___137_6769.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6769.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6769.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6769.current_module_name)
                      } in
                    let uu____6770 =
                      let uu____6773 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6773 env3 in
                    (match uu____6770 with
                     | (pre1,decls'') ->
                         let uu____6778 =
                           let uu____6781 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6781 env3 in
                         (match uu____6778 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6788 =
                                let uu____6789 =
                                  let uu____6795 =
                                    let uu____6796 =
                                      let uu____6799 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6799, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6796 in
                                  (pats, vars, uu____6795) in
                                FStar_SMTEncoding_Util.mkForall uu____6789 in
                              (uu____6788, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6812 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6812
        then
          let uu____6813 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6814 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6813 uu____6814
        else () in
      let enc f r l =
        let uu____6841 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6854 = encode_term (fst x) env in
                 match uu____6854 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6841 with
        | (decls,args) ->
            let uu____6871 =
              let uu___138_6872 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6872.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6872.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6871, decls) in
      let const_op f r uu____6897 = let uu____6906 = f r in (uu____6906, []) in
      let un_op f l =
        let uu____6922 = FStar_List.hd l in FStar_All.pipe_left f uu____6922 in
      let bin_op f uu___111_6935 =
        match uu___111_6935 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6943 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6970 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6979  ->
                 match uu____6979 with
                 | (t,uu____6987) ->
                     let uu____6988 = encode_formula t env in
                     (match uu____6988 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6970 with
        | (decls,phis) ->
            let uu____7005 =
              let uu___139_7006 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_7006.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_7006.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____7005, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____7045  ->
               match uu____7045 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____7059) -> false
                    | uu____7060 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____7073 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____7073
        else
          (let uu____7088 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____7088 r rf) in
      let mk_imp1 r uu___112_7107 =
        match uu___112_7107 with
        | (lhs,uu____7111)::(rhs,uu____7113)::[] ->
            let uu____7134 = encode_formula rhs env in
            (match uu____7134 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____7143) ->
                      (l1, decls1)
                  | uu____7146 ->
                      let uu____7147 = encode_formula lhs env in
                      (match uu____7147 with
                       | (l2,decls2) ->
                           let uu____7154 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____7154, (FStar_List.append decls1 decls2)))))
        | uu____7156 -> failwith "impossible" in
      let mk_ite r uu___113_7171 =
        match uu___113_7171 with
        | (guard,uu____7175)::(_then,uu____7177)::(_else,uu____7179)::[] ->
            let uu____7208 = encode_formula guard env in
            (match uu____7208 with
             | (g,decls1) ->
                 let uu____7215 = encode_formula _then env in
                 (match uu____7215 with
                  | (t,decls2) ->
                      let uu____7222 = encode_formula _else env in
                      (match uu____7222 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7231 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7250 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7250 in
      let connectives =
        let uu____7262 =
          let uu____7271 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____7271) in
        let uu____7284 =
          let uu____7294 =
            let uu____7303 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____7303) in
          let uu____7316 =
            let uu____7326 =
              let uu____7336 =
                let uu____7345 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____7345) in
              let uu____7358 =
                let uu____7368 =
                  let uu____7378 =
                    let uu____7387 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____7387) in
                  [uu____7378;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____7368 in
              uu____7336 :: uu____7358 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____7326 in
          uu____7294 :: uu____7316 in
        uu____7262 :: uu____7284 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7603 = encode_formula phi' env in
            (match uu____7603 with
             | (phi2,decls) ->
                 let uu____7610 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7610, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7611 ->
            let uu____7616 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7616 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7645 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7645 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7653;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7655;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7671 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7671 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7703::(x,uu____7705)::(t,uu____7707)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7741 = encode_term x env in
                 (match uu____7741 with
                  | (x1,decls) ->
                      let uu____7748 = encode_term t env in
                      (match uu____7748 with
                       | (t1,decls') ->
                           let uu____7755 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7755, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7759)::(msg,uu____7761)::(phi2,uu____7763)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7797 =
                   let uu____7800 =
                     let uu____7801 = FStar_Syntax_Subst.compress r in
                     uu____7801.FStar_Syntax_Syntax.n in
                   let uu____7804 =
                     let uu____7805 = FStar_Syntax_Subst.compress msg in
                     uu____7805.FStar_Syntax_Syntax.n in
                   (uu____7800, uu____7804) in
                 (match uu____7797 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7812))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7828 -> fallback phi2)
             | uu____7831 when head_redex env head2 ->
                 let uu____7839 = whnf env phi1 in
                 encode_formula uu____7839 env
             | uu____7840 ->
                 let uu____7848 = encode_term phi1 env in
                 (match uu____7848 with
                  | (tt,decls) ->
                      let uu____7855 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7856 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7856.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7856.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7855, decls)))
        | uu____7859 ->
            let uu____7860 = encode_term phi1 env in
            (match uu____7860 with
             | (tt,decls) ->
                 let uu____7867 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7868 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7868.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7868.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7867, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7895 = encode_binders None bs env1 in
        match uu____7895 with
        | (vars,guards,env2,decls,uu____7917) ->
            let uu____7924 =
              let uu____7931 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7954 =
                          let uu____7959 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7973  ->
                                    match uu____7973 with
                                    | (t,uu____7979) ->
                                        encode_term t
                                          (let uu___142_7980 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7980.bindings);
                                             depth = (uu___142_7980.depth);
                                             tcenv = (uu___142_7980.tcenv);
                                             warn = (uu___142_7980.warn);
                                             cache = (uu___142_7980.cache);
                                             nolabels =
                                               (uu___142_7980.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7980.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7980.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7959 FStar_List.unzip in
                        match uu____7954 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7931 FStar_List.unzip in
            (match uu____7924 with
             | (pats,decls') ->
                 let uu____8032 = encode_formula body env2 in
                 (match uu____8032 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____8051;
                             FStar_SMTEncoding_Term.rng = uu____8052;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____8060 -> guards in
                      let uu____8063 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____8063, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____8097  ->
                   match uu____8097 with
                   | (x,uu____8101) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____8107 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____8113 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____8113) uu____8107 tl1 in
             let uu____8115 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____8127  ->
                       match uu____8127 with
                       | (b,uu____8131) ->
                           let uu____8132 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____8132)) in
             (match uu____8115 with
              | None  -> ()
              | Some (x,uu____8136) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____8146 =
                    let uu____8147 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____8147 in
                  FStar_Errors.warn pos uu____8146) in
       let uu____8148 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____8148 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____8154 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____8190  ->
                     match uu____8190 with
                     | (l,uu____8200) -> FStar_Ident.lid_equals op l)) in
           (match uu____8154 with
            | None  -> fallback phi1
            | Some (uu____8223,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8252 = encode_q_body env vars pats body in
             match uu____8252 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8278 =
                     let uu____8284 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8284) in
                   FStar_SMTEncoding_Term.mkForall uu____8278
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8296 = encode_q_body env vars pats body in
             match uu____8296 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8321 =
                   let uu____8322 =
                     let uu____8328 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8328) in
                   FStar_SMTEncoding_Term.mkExists uu____8322
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8321, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let __proj__Mkprims_t__item__mk:
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list)
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
  let uu____8407 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8407 with
  | (asym,a) ->
      let uu____8412 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8412 with
       | (xsym,x) ->
           let uu____8417 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8417 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8447 =
                      let uu____8453 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____8453, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8447 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____8468 =
                      let uu____8472 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8472) in
                    FStar_SMTEncoding_Util.mkApp uu____8468 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8480 =
                    let uu____8482 =
                      let uu____8484 =
                        let uu____8486 =
                          let uu____8487 =
                            let uu____8491 =
                              let uu____8492 =
                                let uu____8498 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8498) in
                              FStar_SMTEncoding_Util.mkForall uu____8492 in
                            (uu____8491, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8487 in
                        let uu____8507 =
                          let uu____8509 =
                            let uu____8510 =
                              let uu____8514 =
                                let uu____8515 =
                                  let uu____8521 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____8521) in
                                FStar_SMTEncoding_Util.mkForall uu____8515 in
                              (uu____8514,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____8510 in
                          [uu____8509] in
                        uu____8486 :: uu____8507 in
                      xtok_decl :: uu____8484 in
                    xname_decl :: uu____8482 in
                  (xtok1, uu____8480) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____8570 =
                    let uu____8578 =
                      let uu____8584 =
                        let uu____8585 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8585 in
                      quant axy uu____8584 in
                    (FStar_Syntax_Const.op_Eq, uu____8578) in
                  let uu____8591 =
                    let uu____8600 =
                      let uu____8608 =
                        let uu____8614 =
                          let uu____8615 =
                            let uu____8616 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8616 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8615 in
                        quant axy uu____8614 in
                      (FStar_Syntax_Const.op_notEq, uu____8608) in
                    let uu____8622 =
                      let uu____8631 =
                        let uu____8639 =
                          let uu____8645 =
                            let uu____8646 =
                              let uu____8647 =
                                let uu____8650 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8651 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8650, uu____8651) in
                              FStar_SMTEncoding_Util.mkLT uu____8647 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8646 in
                          quant xy uu____8645 in
                        (FStar_Syntax_Const.op_LT, uu____8639) in
                      let uu____8657 =
                        let uu____8666 =
                          let uu____8674 =
                            let uu____8680 =
                              let uu____8681 =
                                let uu____8682 =
                                  let uu____8685 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8686 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8685, uu____8686) in
                                FStar_SMTEncoding_Util.mkLTE uu____8682 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8681 in
                            quant xy uu____8680 in
                          (FStar_Syntax_Const.op_LTE, uu____8674) in
                        let uu____8692 =
                          let uu____8701 =
                            let uu____8709 =
                              let uu____8715 =
                                let uu____8716 =
                                  let uu____8717 =
                                    let uu____8720 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8721 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8720, uu____8721) in
                                  FStar_SMTEncoding_Util.mkGT uu____8717 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8716 in
                              quant xy uu____8715 in
                            (FStar_Syntax_Const.op_GT, uu____8709) in
                          let uu____8727 =
                            let uu____8736 =
                              let uu____8744 =
                                let uu____8750 =
                                  let uu____8751 =
                                    let uu____8752 =
                                      let uu____8755 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8756 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8755, uu____8756) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8752 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8751 in
                                quant xy uu____8750 in
                              (FStar_Syntax_Const.op_GTE, uu____8744) in
                            let uu____8762 =
                              let uu____8771 =
                                let uu____8779 =
                                  let uu____8785 =
                                    let uu____8786 =
                                      let uu____8787 =
                                        let uu____8790 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8791 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8790, uu____8791) in
                                      FStar_SMTEncoding_Util.mkSub uu____8787 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8786 in
                                  quant xy uu____8785 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8779) in
                              let uu____8797 =
                                let uu____8806 =
                                  let uu____8814 =
                                    let uu____8820 =
                                      let uu____8821 =
                                        let uu____8822 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8822 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8821 in
                                    quant qx uu____8820 in
                                  (FStar_Syntax_Const.op_Minus, uu____8814) in
                                let uu____8828 =
                                  let uu____8837 =
                                    let uu____8845 =
                                      let uu____8851 =
                                        let uu____8852 =
                                          let uu____8853 =
                                            let uu____8856 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8857 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8856, uu____8857) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8853 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8852 in
                                      quant xy uu____8851 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8845) in
                                  let uu____8863 =
                                    let uu____8872 =
                                      let uu____8880 =
                                        let uu____8886 =
                                          let uu____8887 =
                                            let uu____8888 =
                                              let uu____8891 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8892 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8891, uu____8892) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8888 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8887 in
                                        quant xy uu____8886 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8880) in
                                    let uu____8898 =
                                      let uu____8907 =
                                        let uu____8915 =
                                          let uu____8921 =
                                            let uu____8922 =
                                              let uu____8923 =
                                                let uu____8926 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8927 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8926, uu____8927) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8923 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8922 in
                                          quant xy uu____8921 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8915) in
                                      let uu____8933 =
                                        let uu____8942 =
                                          let uu____8950 =
                                            let uu____8956 =
                                              let uu____8957 =
                                                let uu____8958 =
                                                  let uu____8961 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8962 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8961, uu____8962) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8958 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8957 in
                                            quant xy uu____8956 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8950) in
                                        let uu____8968 =
                                          let uu____8977 =
                                            let uu____8985 =
                                              let uu____8991 =
                                                let uu____8992 =
                                                  let uu____8993 =
                                                    let uu____8996 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8997 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8996, uu____8997) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8993 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8992 in
                                              quant xy uu____8991 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8985) in
                                          let uu____9003 =
                                            let uu____9012 =
                                              let uu____9020 =
                                                let uu____9026 =
                                                  let uu____9027 =
                                                    let uu____9028 =
                                                      let uu____9031 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____9032 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____9031,
                                                        uu____9032) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____9028 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____9027 in
                                                quant xy uu____9026 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____9020) in
                                            let uu____9038 =
                                              let uu____9047 =
                                                let uu____9055 =
                                                  let uu____9061 =
                                                    let uu____9062 =
                                                      let uu____9063 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____9063 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____9062 in
                                                  quant qx uu____9061 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____9055) in
                                              [uu____9047] in
                                            uu____9012 :: uu____9038 in
                                          uu____8977 :: uu____9003 in
                                        uu____8942 :: uu____8968 in
                                      uu____8907 :: uu____8933 in
                                    uu____8872 :: uu____8898 in
                                  uu____8837 :: uu____8863 in
                                uu____8806 :: uu____8828 in
                              uu____8771 :: uu____8797 in
                            uu____8736 :: uu____8762 in
                          uu____8701 :: uu____8727 in
                        uu____8666 :: uu____8692 in
                      uu____8631 :: uu____8657 in
                    uu____8600 :: uu____8622 in
                  uu____8570 :: uu____8591 in
                let mk1 l v1 =
                  let uu____9191 =
                    let uu____9196 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9228  ->
                              match uu____9228 with
                              | (l',uu____9237) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____9196
                      (FStar_Option.map
                         (fun uu____9270  ->
                            match uu____9270 with | (uu____9281,b) -> b v1)) in
                  FStar_All.pipe_right uu____9191 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9322  ->
                          match uu____9322 with
                          | (l',uu____9331) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____9360 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9360 with
        | (xxsym,xx) ->
            let uu____9365 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9365 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____9373 =
                   let uu____9377 =
                     let uu____9378 =
                       let uu____9384 =
                         let uu____9385 =
                           let uu____9388 =
                             let uu____9389 =
                               let uu____9392 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9392) in
                             FStar_SMTEncoding_Util.mkEq uu____9389 in
                           (xx_has_type, uu____9388) in
                         FStar_SMTEncoding_Util.mkImp uu____9385 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9384) in
                     FStar_SMTEncoding_Util.mkForall uu____9378 in
                   let uu____9405 =
                     let uu____9406 =
                       let uu____9407 =
                         let uu____9408 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9408 in
                       Prims.strcat module_name uu____9407 in
                     varops.mk_unique uu____9406 in
                   (uu____9377, (Some "pretyping"), uu____9405) in
                 FStar_SMTEncoding_Util.mkAssume uu____9373)
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
    let uu____9442 =
      let uu____9443 =
        let uu____9447 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9447, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9443 in
    let uu____9449 =
      let uu____9451 =
        let uu____9452 =
          let uu____9456 =
            let uu____9457 =
              let uu____9463 =
                let uu____9464 =
                  let uu____9467 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9467) in
                FStar_SMTEncoding_Util.mkImp uu____9464 in
              ([[typing_pred]], [xx], uu____9463) in
            mkForall_fuel uu____9457 in
          (uu____9456, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9452 in
      [uu____9451] in
    uu____9442 :: uu____9449 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9495 =
      let uu____9496 =
        let uu____9500 =
          let uu____9501 =
            let uu____9507 =
              let uu____9510 =
                let uu____9512 = FStar_SMTEncoding_Term.boxBool b in
                [uu____9512] in
              [uu____9510] in
            let uu____9515 =
              let uu____9516 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____9516 tt in
            (uu____9507, [bb], uu____9515) in
          FStar_SMTEncoding_Util.mkForall uu____9501 in
        (uu____9500, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9496 in
    let uu____9527 =
      let uu____9529 =
        let uu____9530 =
          let uu____9534 =
            let uu____9535 =
              let uu____9541 =
                let uu____9542 =
                  let uu____9545 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____9545) in
                FStar_SMTEncoding_Util.mkImp uu____9542 in
              ([[typing_pred]], [xx], uu____9541) in
            mkForall_fuel uu____9535 in
          (uu____9534, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9530 in
      [uu____9529] in
    uu____9495 :: uu____9527 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____9579 =
        let uu____9580 =
          let uu____9584 =
            let uu____9586 =
              let uu____9588 =
                let uu____9590 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9591 =
                  let uu____9593 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9593] in
                uu____9590 :: uu____9591 in
              tt :: uu____9588 in
            tt :: uu____9586 in
          ("Prims.Precedes", uu____9584) in
        FStar_SMTEncoding_Util.mkApp uu____9580 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9579 in
    let precedes_y_x =
      let uu____9596 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9596 in
    let uu____9598 =
      let uu____9599 =
        let uu____9603 =
          let uu____9604 =
            let uu____9610 =
              let uu____9613 =
                let uu____9615 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9615] in
              [uu____9613] in
            let uu____9618 =
              let uu____9619 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9619 tt in
            (uu____9610, [bb], uu____9618) in
          FStar_SMTEncoding_Util.mkForall uu____9604 in
        (uu____9603, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9599 in
    let uu____9630 =
      let uu____9632 =
        let uu____9633 =
          let uu____9637 =
            let uu____9638 =
              let uu____9644 =
                let uu____9645 =
                  let uu____9648 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9648) in
                FStar_SMTEncoding_Util.mkImp uu____9645 in
              ([[typing_pred]], [xx], uu____9644) in
            mkForall_fuel uu____9638 in
          (uu____9637, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9633 in
      let uu____9661 =
        let uu____9663 =
          let uu____9664 =
            let uu____9668 =
              let uu____9669 =
                let uu____9675 =
                  let uu____9676 =
                    let uu____9679 =
                      let uu____9680 =
                        let uu____9682 =
                          let uu____9684 =
                            let uu____9686 =
                              let uu____9687 =
                                let uu____9690 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9691 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9690, uu____9691) in
                              FStar_SMTEncoding_Util.mkGT uu____9687 in
                            let uu____9692 =
                              let uu____9694 =
                                let uu____9695 =
                                  let uu____9698 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9699 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9698, uu____9699) in
                                FStar_SMTEncoding_Util.mkGTE uu____9695 in
                              let uu____9700 =
                                let uu____9702 =
                                  let uu____9703 =
                                    let uu____9706 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9707 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9706, uu____9707) in
                                  FStar_SMTEncoding_Util.mkLT uu____9703 in
                                [uu____9702] in
                              uu____9694 :: uu____9700 in
                            uu____9686 :: uu____9692 in
                          typing_pred_y :: uu____9684 in
                        typing_pred :: uu____9682 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9680 in
                    (uu____9679, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9676 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9675) in
              mkForall_fuel uu____9669 in
            (uu____9668, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9664 in
        [uu____9663] in
      uu____9632 :: uu____9661 in
    uu____9598 :: uu____9630 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9737 =
      let uu____9738 =
        let uu____9742 =
          let uu____9743 =
            let uu____9749 =
              let uu____9752 =
                let uu____9754 = FStar_SMTEncoding_Term.boxString b in
                [uu____9754] in
              [uu____9752] in
            let uu____9757 =
              let uu____9758 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9758 tt in
            (uu____9749, [bb], uu____9757) in
          FStar_SMTEncoding_Util.mkForall uu____9743 in
        (uu____9742, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9738 in
    let uu____9769 =
      let uu____9771 =
        let uu____9772 =
          let uu____9776 =
            let uu____9777 =
              let uu____9783 =
                let uu____9784 =
                  let uu____9787 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9787) in
                FStar_SMTEncoding_Util.mkImp uu____9784 in
              ([[typing_pred]], [xx], uu____9783) in
            mkForall_fuel uu____9777 in
          (uu____9776, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9772 in
      [uu____9771] in
    uu____9737 :: uu____9769 in
  let mk_ref1 env reft_name uu____9809 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9820 =
        let uu____9824 =
          let uu____9826 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9826] in
        (reft_name, uu____9824) in
      FStar_SMTEncoding_Util.mkApp uu____9820 in
    let refb =
      let uu____9829 =
        let uu____9833 =
          let uu____9835 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9835] in
        (reft_name, uu____9833) in
      FStar_SMTEncoding_Util.mkApp uu____9829 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9839 =
      let uu____9840 =
        let uu____9844 =
          let uu____9845 =
            let uu____9851 =
              let uu____9852 =
                let uu____9855 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9855) in
              FStar_SMTEncoding_Util.mkImp uu____9852 in
            ([[typing_pred]], [xx; aa], uu____9851) in
          mkForall_fuel uu____9845 in
        (uu____9844, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9840 in
    [uu____9839] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9895 =
      let uu____9896 =
        let uu____9900 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9900, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9896 in
    [uu____9895] in
  let mk_and_interp env conj uu____9911 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9928 =
      let uu____9929 =
        let uu____9933 =
          let uu____9934 =
            let uu____9940 =
              let uu____9941 =
                let uu____9944 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9944, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9941 in
            ([[l_and_a_b]], [aa; bb], uu____9940) in
          FStar_SMTEncoding_Util.mkForall uu____9934 in
        (uu____9933, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9929 in
    [uu____9928] in
  let mk_or_interp env disj uu____9968 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9985 =
      let uu____9986 =
        let uu____9990 =
          let uu____9991 =
            let uu____9997 =
              let uu____9998 =
                let uu____10001 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____10001, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9998 in
            ([[l_or_a_b]], [aa; bb], uu____9997) in
          FStar_SMTEncoding_Util.mkForall uu____9991 in
        (uu____9990, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9986 in
    [uu____9985] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____10042 =
      let uu____10043 =
        let uu____10047 =
          let uu____10048 =
            let uu____10054 =
              let uu____10055 =
                let uu____10058 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10058, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10055 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____10054) in
          FStar_SMTEncoding_Util.mkForall uu____10048 in
        (uu____10047, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10043 in
    [uu____10042] in
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
    let uu____10105 =
      let uu____10106 =
        let uu____10110 =
          let uu____10111 =
            let uu____10117 =
              let uu____10118 =
                let uu____10121 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____10121, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10118 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____10117) in
          FStar_SMTEncoding_Util.mkForall uu____10111 in
        (uu____10110, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10106 in
    [uu____10105] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10166 =
      let uu____10167 =
        let uu____10171 =
          let uu____10172 =
            let uu____10178 =
              let uu____10179 =
                let uu____10182 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____10182, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10179 in
            ([[l_imp_a_b]], [aa; bb], uu____10178) in
          FStar_SMTEncoding_Util.mkForall uu____10172 in
        (uu____10171, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10167 in
    [uu____10166] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10223 =
      let uu____10224 =
        let uu____10228 =
          let uu____10229 =
            let uu____10235 =
              let uu____10236 =
                let uu____10239 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10239, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10236 in
            ([[l_iff_a_b]], [aa; bb], uu____10235) in
          FStar_SMTEncoding_Util.mkForall uu____10229 in
        (uu____10228, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10224 in
    [uu____10223] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____10273 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10273 in
    let uu____10275 =
      let uu____10276 =
        let uu____10280 =
          let uu____10281 =
            let uu____10287 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10287) in
          FStar_SMTEncoding_Util.mkForall uu____10281 in
        (uu____10280, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10276 in
    [uu____10275] in
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
      let uu____10327 =
        let uu____10331 =
          let uu____10333 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10333] in
        ("Valid", uu____10331) in
      FStar_SMTEncoding_Util.mkApp uu____10327 in
    let uu____10335 =
      let uu____10336 =
        let uu____10340 =
          let uu____10341 =
            let uu____10347 =
              let uu____10348 =
                let uu____10351 =
                  let uu____10352 =
                    let uu____10358 =
                      let uu____10361 =
                        let uu____10363 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10363] in
                      [uu____10361] in
                    let uu____10366 =
                      let uu____10367 =
                        let uu____10370 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10370, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10367 in
                    (uu____10358, [xx1], uu____10366) in
                  FStar_SMTEncoding_Util.mkForall uu____10352 in
                (uu____10351, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10348 in
            ([[l_forall_a_b]], [aa; bb], uu____10347) in
          FStar_SMTEncoding_Util.mkForall uu____10341 in
        (uu____10340, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10336 in
    [uu____10335] in
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
      let uu____10421 =
        let uu____10425 =
          let uu____10427 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10427] in
        ("Valid", uu____10425) in
      FStar_SMTEncoding_Util.mkApp uu____10421 in
    let uu____10429 =
      let uu____10430 =
        let uu____10434 =
          let uu____10435 =
            let uu____10441 =
              let uu____10442 =
                let uu____10445 =
                  let uu____10446 =
                    let uu____10452 =
                      let uu____10455 =
                        let uu____10457 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10457] in
                      [uu____10455] in
                    let uu____10460 =
                      let uu____10461 =
                        let uu____10464 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10464, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10461 in
                    (uu____10452, [xx1], uu____10460) in
                  FStar_SMTEncoding_Util.mkExists uu____10446 in
                (uu____10445, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10442 in
            ([[l_exists_a_b]], [aa; bb], uu____10441) in
          FStar_SMTEncoding_Util.mkForall uu____10435 in
        (uu____10434, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10430 in
    [uu____10429] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____10500 =
      let uu____10501 =
        let uu____10505 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____10506 = varops.mk_unique "typing_range_const" in
        (uu____10505, (Some "Range_const typing"), uu____10506) in
      FStar_SMTEncoding_Util.mkAssume uu____10501 in
    [uu____10500] in
  let prims1 =
    [(FStar_Syntax_Const.unit_lid, mk_unit);
    (FStar_Syntax_Const.bool_lid, mk_bool);
    (FStar_Syntax_Const.int_lid, mk_int);
    (FStar_Syntax_Const.string_lid, mk_str);
    (FStar_Syntax_Const.ref_lid, mk_ref1);
    (FStar_Syntax_Const.true_lid, mk_true_interp);
    (FStar_Syntax_Const.false_lid, mk_false_interp);
    (FStar_Syntax_Const.and_lid, mk_and_interp);
    (FStar_Syntax_Const.or_lid, mk_or_interp);
    (FStar_Syntax_Const.eq2_lid, mk_eq2_interp);
    (FStar_Syntax_Const.eq3_lid, mk_eq3_interp);
    (FStar_Syntax_Const.imp_lid, mk_imp_interp);
    (FStar_Syntax_Const.iff_lid, mk_iff_interp);
    (FStar_Syntax_Const.not_lid, mk_not_interp);
    (FStar_Syntax_Const.forall_lid, mk_forall_interp);
    (FStar_Syntax_Const.exists_lid, mk_exists_interp);
    (FStar_Syntax_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____10768 =
            FStar_Util.find_opt
              (fun uu____10786  ->
                 match uu____10786 with
                 | (l,uu____10796) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10768 with
          | None  -> []
          | Some (uu____10818,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10858 = encode_function_type_as_formula t env in
        match uu____10858 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____10895 =
              (let uu____10896 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10896) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10895
            then
              let uu____10900 = new_term_constant_and_tok_from_lid env lid in
              match uu____10900 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10912 =
                      let uu____10913 = FStar_Syntax_Subst.compress t_norm in
                      uu____10913.FStar_Syntax_Syntax.n in
                    match uu____10912 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10918) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10935  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10938 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____10947 = prims.is lid in
               if uu____10947
               then
                 let vname = varops.new_fvar lid in
                 let uu____10952 = prims.mk lid vname in
                 match uu____10952 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10967 =
                    let uu____10973 = curried_arrow_formals_comp t_norm in
                    match uu____10973 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10984 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10984
                          then
                            let uu____10985 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10986 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10986.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10986.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10986.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10986.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10986.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10986.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10986.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10986.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10986.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10986.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10986.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10986.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10986.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10986.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10986.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10986.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10986.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10986.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10986.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10986.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10986.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10986.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10986.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10986.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10986.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10986.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10985
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10993 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10993)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10967 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____11020 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____11020 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____11033 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___114_11057  ->
                                     match uu___114_11057 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____11060 =
                                           FStar_Util.prefix vars in
                                         (match uu____11060 with
                                          | (uu____11071,(xxsym,uu____11073))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____11083 =
                                                let uu____11084 =
                                                  let uu____11088 =
                                                    let uu____11089 =
                                                      let uu____11095 =
                                                        let uu____11096 =
                                                          let uu____11099 =
                                                            let uu____11100 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____11100 in
                                                          (vapp, uu____11099) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____11096 in
                                                      ([[vapp]], vars,
                                                        uu____11095) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11089 in
                                                  (uu____11088,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11084 in
                                              [uu____11083])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____11111 =
                                           FStar_Util.prefix vars in
                                         (match uu____11111 with
                                          | (uu____11122,(xxsym,uu____11124))
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
                                              let uu____11138 =
                                                let uu____11139 =
                                                  let uu____11143 =
                                                    let uu____11144 =
                                                      let uu____11150 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____11150) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____11144 in
                                                  (uu____11143,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____11139 in
                                              [uu____11138])
                                     | uu____11159 -> [])) in
                           let uu____11160 = encode_binders None formals env1 in
                           (match uu____11160 with
                            | (vars,guards,env',decls1,uu____11176) ->
                                let uu____11183 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____11188 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____11188, decls1)
                                  | Some p ->
                                      let uu____11190 = encode_formula p env' in
                                      (match uu____11190 with
                                       | (g,ds) ->
                                           let uu____11197 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____11197,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____11183 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____11206 =
                                         let uu____11210 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____11210) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____11206 in
                                     let uu____11215 =
                                       let vname_decl =
                                         let uu____11220 =
                                           let uu____11226 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11231  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11226,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____11220 in
                                       let uu____11236 =
                                         let env2 =
                                           let uu___144_11240 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11240.bindings);
                                             depth = (uu___144_11240.depth);
                                             tcenv = (uu___144_11240.tcenv);
                                             warn = (uu___144_11240.warn);
                                             cache = (uu___144_11240.cache);
                                             nolabels =
                                               (uu___144_11240.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11240.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11240.current_module_name)
                                           } in
                                         let uu____11241 =
                                           let uu____11242 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11242 in
                                         if uu____11241
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____11236 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11252::uu____11253 ->
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
                                                   let uu____11276 =
                                                     let uu____11282 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11282) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11276 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11296 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____11298 =
                                             match formals with
                                             | [] ->
                                                 let uu____11307 =
                                                   let uu____11308 =
                                                     let uu____11310 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_44  ->
                                                          Some _0_44)
                                                       uu____11310 in
                                                   push_free_var env1 lid
                                                     vname uu____11308 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11307)
                                             | uu____11313 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____11318 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11318 in
                                                 let name_tok_corr =
                                                   let uu____11320 =
                                                     let uu____11324 =
                                                       let uu____11325 =
                                                         let uu____11331 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11331) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11325 in
                                                     (uu____11324,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11320 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____11298 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____11215 with
                                      | (decls2,env2) ->
                                          let uu____11355 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11360 =
                                              encode_term res_t1 env' in
                                            match uu____11360 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11368 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11368,
                                                  decls) in
                                          (match uu____11355 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11376 =
                                                   let uu____11380 =
                                                     let uu____11381 =
                                                       let uu____11387 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11387) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11381 in
                                                   (uu____11380,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11376 in
                                               let freshness =
                                                 let uu____11396 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11396
                                                 then
                                                   let uu____11399 =
                                                     let uu____11400 =
                                                       let uu____11406 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____11412 =
                                                         varops.next_id () in
                                                       (vname, uu____11406,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11412) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11400 in
                                                   let uu____11414 =
                                                     let uu____11416 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11416] in
                                                   uu____11399 :: uu____11414
                                                 else [] in
                                               let g =
                                                 let uu____11420 =
                                                   let uu____11422 =
                                                     let uu____11424 =
                                                       let uu____11426 =
                                                         let uu____11428 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____11428 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11426 in
                                                     FStar_List.append decls3
                                                       uu____11424 in
                                                   FStar_List.append decls2
                                                     uu____11422 in
                                                 FStar_List.append decls11
                                                   uu____11420 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____11454 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11454 with
          | None  ->
              let uu____11477 = encode_free_var env x t t_norm [] in
              (match uu____11477 with
               | (decls,env1) ->
                   let uu____11492 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____11492 with
                    | (n1,x',uu____11511) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____11523) -> ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____11560 = encode_free_var env lid t tt quals in
          match uu____11560 with
          | (decls,env1) ->
              let uu____11571 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____11571
              then
                let uu____11575 =
                  let uu____11577 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11577 in
                (uu____11575, env1)
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____11608  ->
                fun lb  ->
                  match uu____11608 with
                  | (decls,env1) ->
                      let uu____11620 =
                        let uu____11624 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11624
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11620 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____11639 = FStar_Syntax_Util.head_and_args t in
    match uu____11639 with
    | (hd1,args) ->
        let uu____11665 =
          let uu____11666 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11666.FStar_Syntax_Syntax.n in
        (match uu____11665 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11670,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11683 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____11701  ->
      fun quals  ->
        match uu____11701 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11751 = FStar_Util.first_N nbinders formals in
              match uu____11751 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11793  ->
                         fun uu____11794  ->
                           match (uu____11793, uu____11794) with
                           | ((formal,uu____11804),(binder,uu____11806)) ->
                               let uu____11811 =
                                 let uu____11816 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11816) in
                               FStar_Syntax_Syntax.NT uu____11811) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11821 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11835  ->
                              match uu____11835 with
                              | (x,i) ->
                                  let uu____11842 =
                                    let uu___145_11843 = x in
                                    let uu____11844 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11843.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11843.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11844
                                    } in
                                  (uu____11842, i))) in
                    FStar_All.pipe_right uu____11821
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11856 =
                      let uu____11858 =
                        let uu____11859 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11859.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_45  -> Some _0_45)
                        uu____11858 in
                    let uu____11863 =
                      let uu____11864 = FStar_Syntax_Subst.compress body in
                      let uu____11865 =
                        let uu____11866 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11866 in
                      FStar_Syntax_Syntax.extend_app_n uu____11864
                        uu____11865 in
                    uu____11863 uu____11856 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11908 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11908
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11909 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11909.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11909.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11909.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11909.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11909.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11909.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11909.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11909.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11909.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11909.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11909.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11909.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11909.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11909.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11909.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11909.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11909.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11909.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11909.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11909.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11909.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11909.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11909.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11909.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11909.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11909.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11930 = FStar_Syntax_Util.abs_formals e in
                match uu____11930 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11979::uu____11980 ->
                         let uu____11988 =
                           let uu____11989 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11989.FStar_Syntax_Syntax.n in
                         (match uu____11988 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12016 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12016 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____12044 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____12044
                                   then
                                     let uu____12067 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____12067 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____12115  ->
                                                   fun uu____12116  ->
                                                     match (uu____12115,
                                                             uu____12116)
                                                     with
                                                     | ((x,uu____12126),
                                                        (b,uu____12128)) ->
                                                         let uu____12133 =
                                                           let uu____12138 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____12138) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____12133)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____12140 =
                                            let uu____12151 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____12151) in
                                          (uu____12140, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____12191 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____12191 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12243) ->
                              let uu____12248 =
                                let uu____12259 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____12259 in
                              (uu____12248, true)
                          | uu____12292 when Prims.op_Negation norm1 ->
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
                          | uu____12294 ->
                              let uu____12295 =
                                let uu____12296 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12297 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12296
                                  uu____12297 in
                              failwith uu____12295)
                     | uu____12310 ->
                         let uu____12311 =
                           let uu____12312 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12312.FStar_Syntax_Syntax.n in
                         (match uu____12311 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12339 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12339 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12357 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12357 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12405 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12433 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____12433
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12440 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____12481  ->
                            fun lb  ->
                              match uu____12481 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____12532 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____12532
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____12535 =
                                      let uu____12543 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____12543
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____12535 with
                                    | (tok,decl,env2) ->
                                        let uu____12568 =
                                          let uu____12575 =
                                            let uu____12581 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12581, tok) in
                                          uu____12575 :: toks in
                                        (uu____12568, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12440 with
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
                        | uu____12683 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____12688 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12688 vars)
                            else
                              (let uu____12690 =
                                 let uu____12694 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12694) in
                               FStar_SMTEncoding_Util.mkApp uu____12690) in
                      let uu____12699 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___115_12701  ->
                                 match uu___115_12701 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12702 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12705 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12705))) in
                      if uu____12699
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12725;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12727;
                                FStar_Syntax_Syntax.lbeff = uu____12728;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12769 =
                                 let uu____12773 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12773 with
                                 | (tcenv',uu____12784,e_t) ->
                                     let uu____12788 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12795 -> failwith "Impossible" in
                                     (match uu____12788 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12804 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12804.bindings);
                                              depth = (uu___149_12804.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12804.warn);
                                              cache = (uu___149_12804.cache);
                                              nolabels =
                                                (uu___149_12804.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12804.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12804.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12804.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12769 with
                                | (env',e1,t_norm1) ->
                                    let uu____12811 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12811 with
                                     | ((binders,body,uu____12823,uu____12824),curry)
                                         ->
                                         ((let uu____12831 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12831
                                           then
                                             let uu____12832 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12833 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12832 uu____12833
                                           else ());
                                          (let uu____12835 =
                                             encode_binders None binders env' in
                                           match uu____12835 with
                                           | (vars,guards,env'1,binder_decls,uu____12851)
                                               ->
                                               let body1 =
                                                 let uu____12859 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12859
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12862 =
                                                 let uu____12867 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12867
                                                 then
                                                   let uu____12873 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12874 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12873, uu____12874)
                                                 else
                                                   (let uu____12880 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12880)) in
                                               (match uu____12862 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12894 =
                                                        let uu____12898 =
                                                          let uu____12899 =
                                                            let uu____12905 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12905) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12899 in
                                                        let uu____12911 =
                                                          let uu____12913 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12913 in
                                                        (uu____12898,
                                                          uu____12911,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12894 in
                                                    let uu____12915 =
                                                      let uu____12917 =
                                                        let uu____12919 =
                                                          let uu____12921 =
                                                            let uu____12923 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12923 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12921 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12919 in
                                                      FStar_List.append
                                                        decls1 uu____12917 in
                                                    (uu____12915, env1))))))
                           | uu____12926 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12945 = varops.fresh "fuel" in
                             (uu____12945, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12948 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12987  ->
                                     fun uu____12988  ->
                                       match (uu____12987, uu____12988) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____13070 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____13070 in
                                           let gtok =
                                             let uu____13072 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____13072 in
                                           let env3 =
                                             let uu____13074 =
                                               let uu____13076 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_46  -> Some _0_46)
                                                 uu____13076 in
                                             push_free_var env2 flid gtok
                                               uu____13074 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12948 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____13162
                                 t_norm uu____13164 =
                                 match (uu____13162, uu____13164) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____13191;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____13192;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____13209 =
                                       let uu____13213 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____13213 with
                                       | (tcenv',uu____13228,e_t) ->
                                           let uu____13232 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13239 ->
                                                 failwith "Impossible" in
                                           (match uu____13232 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13248 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13248.bindings);
                                                    depth =
                                                      (uu___150_13248.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13248.warn);
                                                    cache =
                                                      (uu___150_13248.cache);
                                                    nolabels =
                                                      (uu___150_13248.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13248.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13248.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13248.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____13209 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13258 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____13258
                                            then
                                              let uu____13259 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13260 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13261 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13259 uu____13260
                                                uu____13261
                                            else ());
                                           (let uu____13263 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13263 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13285 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____13285
                                                  then
                                                    let uu____13286 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13287 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13288 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13289 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13286 uu____13287
                                                      uu____13288 uu____13289
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13293 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____13293 with
                                                  | (vars,guards,env'1,binder_decls,uu____13311)
                                                      ->
                                                      let decl_g =
                                                        let uu____13319 =
                                                          let uu____13325 =
                                                            let uu____13327 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13327 in
                                                          (g, uu____13325,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13319 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____13342 =
                                                          let uu____13346 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13346) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13342 in
                                                      let gsapp =
                                                        let uu____13352 =
                                                          let uu____13356 =
                                                            let uu____13358 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13358 ::
                                                              vars_tm in
                                                          (g, uu____13356) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13352 in
                                                      let gmax =
                                                        let uu____13362 =
                                                          let uu____13366 =
                                                            let uu____13368 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13368 ::
                                                              vars_tm in
                                                          (g, uu____13366) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13362 in
                                                      let body1 =
                                                        let uu____13372 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13372
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____13374 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13374 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13385
                                                               =
                                                               let uu____13389
                                                                 =
                                                                 let uu____13390
                                                                   =
                                                                   let uu____13398
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13398) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13390 in
                                                               let uu____13409
                                                                 =
                                                                 let uu____13411
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____13411 in
                                                               (uu____13389,
                                                                 uu____13409,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13385 in
                                                           let eqn_f =
                                                             let uu____13414
                                                               =
                                                               let uu____13418
                                                                 =
                                                                 let uu____13419
                                                                   =
                                                                   let uu____13425
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13425) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13419 in
                                                               (uu____13418,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13414 in
                                                           let eqn_g' =
                                                             let uu____13433
                                                               =
                                                               let uu____13437
                                                                 =
                                                                 let uu____13438
                                                                   =
                                                                   let uu____13444
                                                                    =
                                                                    let uu____13445
                                                                    =
                                                                    let uu____13448
                                                                    =
                                                                    let uu____13449
                                                                    =
                                                                    let uu____13453
                                                                    =
                                                                    let uu____13455
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____13455
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13453) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13449 in
                                                                    (gsapp,
                                                                    uu____13448) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13445 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13444) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13438 in
                                                               (uu____13437,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13433 in
                                                           let uu____13467 =
                                                             let uu____13472
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____13472
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____13489)
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
                                                                    let uu____13504
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____13504
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____13507
                                                                    =
                                                                    let uu____13511
                                                                    =
                                                                    let uu____13512
                                                                    =
                                                                    let uu____13518
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13518) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13512 in
                                                                    (uu____13511,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13507 in
                                                                 let uu____13529
                                                                   =
                                                                   let uu____13533
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____13533
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____13541
                                                                    =
                                                                    let uu____13543
                                                                    =
                                                                    let uu____13544
                                                                    =
                                                                    let uu____13548
                                                                    =
                                                                    let uu____13549
                                                                    =
                                                                    let uu____13555
                                                                    =
                                                                    let uu____13556
                                                                    =
                                                                    let uu____13559
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____13559,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13556 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13555) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13549 in
                                                                    (uu____13548,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13544 in
                                                                    [uu____13543] in
                                                                    (d3,
                                                                    uu____13541) in
                                                                 (match uu____13529
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____13467
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
                               let uu____13594 =
                                 let uu____13601 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____13637  ->
                                      fun uu____13638  ->
                                        match (uu____13637, uu____13638) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13724 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13724 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13601 in
                               (match uu____13594 with
                                | (decls2,eqns,env01) ->
                                    let uu____13764 =
                                      let isDeclFun uu___116_13772 =
                                        match uu___116_13772 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13773 -> true
                                        | uu____13779 -> false in
                                      let uu____13780 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13780
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13764 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13807 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13807
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____13840 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13840 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13843 = encode_sigelt' env se in
      match uu____13843 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13853 =
                  let uu____13854 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13854 in
                [uu____13853]
            | uu____13855 ->
                let uu____13856 =
                  let uu____13858 =
                    let uu____13859 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13859 in
                  uu____13858 :: g in
                let uu____13860 =
                  let uu____13862 =
                    let uu____13863 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13863 in
                  [uu____13862] in
                FStar_List.append uu____13856 uu____13860 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13873 =
          let uu____13874 = FStar_Syntax_Subst.compress t in
          uu____13874.FStar_Syntax_Syntax.n in
        match uu____13873 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13878)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13881 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13884 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13887 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13889 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13891 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13899 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13902 =
            let uu____13903 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13903 Prims.op_Negation in
          if uu____13902
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13923 ->
                   let uu____13924 =
                     let uu____13927 =
                       let uu____13928 =
                         let uu____13943 =
                           FStar_All.pipe_left (fun _0_47  -> Some _0_47)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13943) in
                       FStar_Syntax_Syntax.Tm_abs uu____13928 in
                     FStar_Syntax_Syntax.mk uu____13927 in
                   uu____13924 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13996 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13996 with
               | (aname,atok,env2) ->
                   let uu____14006 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____14006 with
                    | (formals,uu____14016) ->
                        let uu____14023 =
                          let uu____14026 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____14026 env2 in
                        (match uu____14023 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____14034 =
                                 let uu____14035 =
                                   let uu____14041 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____14049  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____14041,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____14035 in
                               [uu____14034;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____14056 =
                               let aux uu____14085 uu____14086 =
                                 match (uu____14085, uu____14086) with
                                 | ((bv,uu____14113),(env3,acc_sorts,acc)) ->
                                     let uu____14134 = gen_term_var env3 bv in
                                     (match uu____14134 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____14056 with
                              | (uu____14172,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____14186 =
                                      let uu____14190 =
                                        let uu____14191 =
                                          let uu____14197 =
                                            let uu____14198 =
                                              let uu____14201 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____14201) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____14198 in
                                          ([[app]], xs_sorts, uu____14197) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14191 in
                                      (uu____14190, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14186 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____14213 =
                                      let uu____14217 =
                                        let uu____14218 =
                                          let uu____14224 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____14224) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14218 in
                                      (uu____14217,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14213 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____14234 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____14234 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14250,uu____14251)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____14252 = new_term_constant_and_tok_from_lid env lid in
          (match uu____14252 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14263,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____14268 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_14270  ->
                      match uu___117_14270 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____14271 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____14274 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14275 -> false)) in
            Prims.op_Negation uu____14268 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____14281 = encode_top_level_val env fv t quals in
             match uu____14281 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____14293 =
                   let uu____14295 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14295 in
                 (uu____14293, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____14300 = encode_formula f env in
          (match uu____14300 with
           | (f1,decls) ->
               let g =
                 let uu____14309 =
                   let uu____14310 =
                     let uu____14314 =
                       let uu____14316 =
                         let uu____14317 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____14317 in
                       Some uu____14316 in
                     let uu____14318 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____14314, uu____14318) in
                   FStar_SMTEncoding_Util.mkAssume uu____14310 in
                 [uu____14309] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14322,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____14330 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14337 =
                       let uu____14342 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14342.FStar_Syntax_Syntax.fv_name in
                     uu____14337.FStar_Syntax_Syntax.v in
                   let uu____14346 =
                     let uu____14347 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14347 in
                   if uu____14346
                   then
                     let val_decl =
                       let uu___151_14362 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14362.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14362.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____14366 = encode_sigelt' env1 val_decl in
                     match uu____14366 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____14330 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14383,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14385;
                          FStar_Syntax_Syntax.lbtyp = uu____14386;
                          FStar_Syntax_Syntax.lbeff = uu____14387;
                          FStar_Syntax_Syntax.lbdef = uu____14388;_}::[]),uu____14389,uu____14390)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____14404 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14404 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____14427 =
                   let uu____14429 =
                     let uu____14430 =
                       let uu____14434 =
                         let uu____14435 =
                           let uu____14441 =
                             let uu____14442 =
                               let uu____14445 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14445) in
                             FStar_SMTEncoding_Util.mkEq uu____14442 in
                           ([[b2t_x]], [xx], uu____14441) in
                         FStar_SMTEncoding_Util.mkForall uu____14435 in
                       (uu____14434, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14430 in
                   [uu____14429] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____14427 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14462,uu____14463,uu____14464)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___118_14470  ->
                  match uu___118_14470 with
                  | FStar_Syntax_Syntax.Discriminator uu____14471 -> true
                  | uu____14472 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14474,lids,uu____14476) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14483 =
                     let uu____14484 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14484.FStar_Ident.idText in
                   uu____14483 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___119_14486  ->
                     match uu___119_14486 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14487 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14490,uu____14491)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_14501  ->
                  match uu___120_14501 with
                  | FStar_Syntax_Syntax.Projector uu____14502 -> true
                  | uu____14505 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____14512 = try_lookup_free_var env l in
          (match uu____14512 with
           | Some uu____14516 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_14519 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_14519.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_14519.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____14525,uu____14526) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14538) ->
          let uu____14543 = encode_sigelts env ses in
          (match uu____14543 with
           | (g,env1) ->
               let uu____14553 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___121_14563  ->
                         match uu___121_14563 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____14564;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____14565;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____14566;_}
                             -> false
                         | uu____14568 -> true)) in
               (match uu____14553 with
                | (g',inversions) ->
                    let uu____14577 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___122_14587  ->
                              match uu___122_14587 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14588 ->
                                  true
                              | uu____14594 -> false)) in
                    (match uu____14577 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____14605,tps,k,uu____14608,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___123_14618  ->
                    match uu___123_14618 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14619 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14626 = c in
              match uu____14626 with
              | (name,args,uu____14630,uu____14631,uu____14632) ->
                  let uu____14635 =
                    let uu____14636 =
                      let uu____14642 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14649  ->
                                match uu____14649 with
                                | (uu____14653,sort,uu____14655) -> sort)) in
                      (name, uu____14642, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14636 in
                  [uu____14635]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____14673 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14676 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____14676 FStar_Option.isNone)) in
            if uu____14673
            then []
            else
              (let uu____14693 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14693 with
               | (xxsym,xx) ->
                   let uu____14699 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14710  ->
                             fun l  ->
                               match uu____14710 with
                               | (out,decls) ->
                                   let uu____14722 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14722 with
                                    | (uu____14728,data_t) ->
                                        let uu____14730 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14730 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14759 =
                                                 let uu____14760 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14760.FStar_Syntax_Syntax.n in
                                               match uu____14759 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14768,indices) ->
                                                   indices
                                               | uu____14784 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14796  ->
                                                         match uu____14796
                                                         with
                                                         | (x,uu____14800) ->
                                                             let uu____14801
                                                               =
                                                               let uu____14802
                                                                 =
                                                                 let uu____14806
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14806,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14802 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14801)
                                                    env) in
                                             let uu____14808 =
                                               encode_args indices env1 in
                                             (match uu____14808 with
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
                                                      let uu____14832 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14840
                                                                 =
                                                                 let uu____14843
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14843,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14840)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14832
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14845 =
                                                      let uu____14846 =
                                                        let uu____14849 =
                                                          let uu____14850 =
                                                            let uu____14853 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14853,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14850 in
                                                        (out, uu____14849) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14846 in
                                                    (uu____14845,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14699 with
                    | (data_ax,decls) ->
                        let uu____14861 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14861 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14875 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14875 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14878 =
                                 let uu____14882 =
                                   let uu____14883 =
                                     let uu____14889 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14897 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14889,
                                       uu____14897) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14883 in
                                 let uu____14905 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14882, (Some "inversion axiom"),
                                   uu____14905) in
                               FStar_SMTEncoding_Util.mkAssume uu____14878 in
                             let pattern_guarded_inversion =
                               let uu____14909 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14909
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14920 =
                                   let uu____14921 =
                                     let uu____14925 =
                                       let uu____14926 =
                                         let uu____14932 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14940 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14932, uu____14940) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14926 in
                                     let uu____14948 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14925, (Some "inversion axiom"),
                                       uu____14948) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14921 in
                                 [uu____14920]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14951 =
            let uu____14959 =
              let uu____14960 = FStar_Syntax_Subst.compress k in
              uu____14960.FStar_Syntax_Syntax.n in
            match uu____14959 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14989 -> (tps, k) in
          (match uu____14951 with
           | (formals,res) ->
               let uu____15004 = FStar_Syntax_Subst.open_term formals res in
               (match uu____15004 with
                | (formals1,res1) ->
                    let uu____15011 = encode_binders None formals1 env in
                    (match uu____15011 with
                     | (vars,guards,env',binder_decls,uu____15026) ->
                         let uu____15033 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____15033 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____15046 =
                                  let uu____15050 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____15050) in
                                FStar_SMTEncoding_Util.mkApp uu____15046 in
                              let uu____15055 =
                                let tname_decl =
                                  let uu____15061 =
                                    let uu____15062 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____15077  ->
                                              match uu____15077 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____15085 = varops.next_id () in
                                    (tname, uu____15062,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____15085, false) in
                                  constructor_or_logic_type_decl uu____15061 in
                                let uu____15090 =
                                  match vars with
                                  | [] ->
                                      let uu____15097 =
                                        let uu____15098 =
                                          let uu____15100 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_48  -> Some _0_48)
                                            uu____15100 in
                                        push_free_var env1 t tname
                                          uu____15098 in
                                      ([], uu____15097)
                                  | uu____15104 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____15110 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____15110 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____15119 =
                                          let uu____15123 =
                                            let uu____15124 =
                                              let uu____15132 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____15132) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____15124 in
                                          (uu____15123,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____15119 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____15090 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____15055 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____15155 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____15155 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____15172 =
                                               let uu____15173 =
                                                 let uu____15177 =
                                                   let uu____15178 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____15178 in
                                                 (uu____15177,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15173 in
                                             [uu____15172]
                                           else [] in
                                         let uu____15181 =
                                           let uu____15183 =
                                             let uu____15185 =
                                               let uu____15186 =
                                                 let uu____15190 =
                                                   let uu____15191 =
                                                     let uu____15197 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____15197) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____15191 in
                                                 (uu____15190, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____15186 in
                                             [uu____15185] in
                                           FStar_List.append karr uu____15183 in
                                         FStar_List.append decls1 uu____15181 in
                                   let aux =
                                     let uu____15206 =
                                       let uu____15208 =
                                         inversion_axioms tapp vars in
                                       let uu____15210 =
                                         let uu____15212 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____15212] in
                                       FStar_List.append uu____15208
                                         uu____15210 in
                                     FStar_List.append kindingAx uu____15206 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15217,uu____15218,uu____15219,uu____15220,uu____15221)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15226,t,uu____15228,n_tps,uu____15230) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____15235 = new_term_constant_and_tok_from_lid env d in
          (match uu____15235 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____15246 = FStar_Syntax_Util.arrow_formals t in
               (match uu____15246 with
                | (formals,t_res) ->
                    let uu____15268 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____15268 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____15277 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____15277 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____15315 =
                                            mk_term_projector_name d x in
                                          (uu____15315,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15317 =
                                  let uu____15327 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15327, true) in
                                FStar_All.pipe_right uu____15317
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
                              let uu____15349 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____15349 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15357::uu____15358 ->
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
                                         let uu____15383 =
                                           let uu____15389 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15389) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15383
                                     | uu____15402 -> tok_typing in
                                   let uu____15407 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____15407 with
                                    | (vars',guards',env'',decls_formals,uu____15422)
                                        ->
                                        let uu____15429 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____15429 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15448 ->
                                                   let uu____15452 =
                                                     let uu____15453 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15453 in
                                                   [uu____15452] in
                                             let encode_elim uu____15460 =
                                               let uu____15461 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____15461 with
                                               | (head1,args) ->
                                                   let uu____15490 =
                                                     let uu____15491 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____15491.FStar_Syntax_Syntax.n in
                                                   (match uu____15490 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____15498;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____15499;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____15500;_},uu____15501)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15511 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15511
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____15537
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15545
                                                                    =
                                                                    let uu____15546
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15546 in
                                                                    if
                                                                    uu____15545
                                                                    then
                                                                    let uu____15553
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15553]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15555
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15568
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15568
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15590
                                                                    =
                                                                    let uu____15594
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15594 in
                                                                    (match uu____15590
                                                                    with
                                                                    | 
                                                                    (uu____15601,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15607
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15607
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15609
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15609
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
                                                                 encoded_args in
                                                             (match uu____15555
                                                              with
                                                              | (uu____15617,arg_vars,elim_eqns_or_guards,uu____15620)
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
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____15639
                                                                    =
                                                                    let uu____15643
                                                                    =
                                                                    let uu____15644
                                                                    =
                                                                    let uu____15650
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15656
                                                                    =
                                                                    let uu____15657
                                                                    =
                                                                    let uu____15660
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15660) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15657 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15650,
                                                                    uu____15656) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15644 in
                                                                    (uu____15643,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15639 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15673
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15673,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15675
                                                                    =
                                                                    let uu____15679
                                                                    =
                                                                    let uu____15680
                                                                    =
                                                                    let uu____15686
                                                                    =
                                                                    let uu____15689
                                                                    =
                                                                    let uu____15691
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15691] in
                                                                    [uu____15689] in
                                                                    let uu____15694
                                                                    =
                                                                    let uu____15695
                                                                    =
                                                                    let uu____15698
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15699
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15698,
                                                                    uu____15699) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15695 in
                                                                    (uu____15686,
                                                                    [x],
                                                                    uu____15694) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15680 in
                                                                    let uu____15709
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15679,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15709) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15675
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15714
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
                                                                    (let uu____15729
                                                                    =
                                                                    let uu____15730
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15730
                                                                    dapp1 in
                                                                    [uu____15729]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15714
                                                                    FStar_List.flatten in
                                                                    let uu____15734
                                                                    =
                                                                    let uu____15738
                                                                    =
                                                                    let uu____15739
                                                                    =
                                                                    let uu____15745
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15751
                                                                    =
                                                                    let uu____15752
                                                                    =
                                                                    let uu____15755
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15755) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15752 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15745,
                                                                    uu____15751) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15739 in
                                                                    (uu____15738,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15734) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15771 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15771
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____15797
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15805
                                                                    =
                                                                    let uu____15806
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15806 in
                                                                    if
                                                                    uu____15805
                                                                    then
                                                                    let uu____15813
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15813]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15815
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15828
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15828
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15850
                                                                    =
                                                                    let uu____15854
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15854 in
                                                                    (match uu____15850
                                                                    with
                                                                    | 
                                                                    (uu____15861,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15867
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15867
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15869
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15869
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
                                                                 encoded_args in
                                                             (match uu____15815
                                                              with
                                                              | (uu____15877,arg_vars,elim_eqns_or_guards,uu____15880)
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
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____15899
                                                                    =
                                                                    let uu____15903
                                                                    =
                                                                    let uu____15904
                                                                    =
                                                                    let uu____15910
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15916
                                                                    =
                                                                    let uu____15917
                                                                    =
                                                                    let uu____15920
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15920) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15917 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15910,
                                                                    uu____15916) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15904 in
                                                                    (uu____15903,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15899 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15933
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15933,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15935
                                                                    =
                                                                    let uu____15939
                                                                    =
                                                                    let uu____15940
                                                                    =
                                                                    let uu____15946
                                                                    =
                                                                    let uu____15949
                                                                    =
                                                                    let uu____15951
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15951] in
                                                                    [uu____15949] in
                                                                    let uu____15954
                                                                    =
                                                                    let uu____15955
                                                                    =
                                                                    let uu____15958
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15959
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15958,
                                                                    uu____15959) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15955 in
                                                                    (uu____15946,
                                                                    [x],
                                                                    uu____15954) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15940 in
                                                                    let uu____15969
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15939,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15969) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15935
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15974
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
                                                                    (let uu____15989
                                                                    =
                                                                    let uu____15990
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15990
                                                                    dapp1 in
                                                                    [uu____15989]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15974
                                                                    FStar_List.flatten in
                                                                    let uu____15994
                                                                    =
                                                                    let uu____15998
                                                                    =
                                                                    let uu____15999
                                                                    =
                                                                    let uu____16005
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____16011
                                                                    =
                                                                    let uu____16012
                                                                    =
                                                                    let uu____16015
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____16015) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____16012 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____16005,
                                                                    uu____16011) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15999 in
                                                                    (uu____15998,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15994) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____16025 ->
                                                        ((let uu____16027 =
                                                            let uu____16028 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____16029 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____16028
                                                              uu____16029 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____16027);
                                                         ([], []))) in
                                             let uu____16032 = encode_elim () in
                                             (match uu____16032 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____16044 =
                                                      let uu____16046 =
                                                        let uu____16048 =
                                                          let uu____16050 =
                                                            let uu____16052 =
                                                              let uu____16053
                                                                =
                                                                let uu____16059
                                                                  =
                                                                  let uu____16061
                                                                    =
                                                                    let uu____16062
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____16062 in
                                                                  Some
                                                                    uu____16061 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____16059) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____16053 in
                                                            [uu____16052] in
                                                          let uu____16065 =
                                                            let uu____16067 =
                                                              let uu____16069
                                                                =
                                                                let uu____16071
                                                                  =
                                                                  let uu____16073
                                                                    =
                                                                    let uu____16075
                                                                    =
                                                                    let uu____16077
                                                                    =
                                                                    let uu____16078
                                                                    =
                                                                    let uu____16082
                                                                    =
                                                                    let uu____16083
                                                                    =
                                                                    let uu____16089
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____16089) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16083 in
                                                                    (uu____16082,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16078 in
                                                                    let uu____16096
                                                                    =
                                                                    let uu____16098
                                                                    =
                                                                    let uu____16099
                                                                    =
                                                                    let uu____16103
                                                                    =
                                                                    let uu____16104
                                                                    =
                                                                    let uu____16110
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____16116
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____16110,
                                                                    uu____16116) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____16104 in
                                                                    (uu____16103,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____16099 in
                                                                    [uu____16098] in
                                                                    uu____16077
                                                                    ::
                                                                    uu____16096 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____16075 in
                                                                  FStar_List.append
                                                                    uu____16073
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____16071 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____16069 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____16067 in
                                                          FStar_List.append
                                                            uu____16050
                                                            uu____16065 in
                                                        FStar_List.append
                                                          decls3 uu____16048 in
                                                      FStar_List.append
                                                        decls2 uu____16046 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____16044 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____16137  ->
              fun se  ->
                match uu____16137 with
                | (g,env1) ->
                    let uu____16149 = encode_sigelt env1 se in
                    (match uu____16149 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____16187 =
        match uu____16187 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____16205 ->
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
                 ((let uu____16210 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____16210
                   then
                     let uu____16211 = FStar_Syntax_Print.bv_to_string x in
                     let uu____16212 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____16213 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16211 uu____16212 uu____16213
                   else ());
                  (let uu____16215 = encode_term t1 env1 in
                   match uu____16215 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____16225 =
                         let uu____16229 =
                           let uu____16230 =
                             let uu____16231 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____16231
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____16230 in
                         new_term_constant_from_string env1 x uu____16229 in
                       (match uu____16225 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____16242 = FStar_Options.log_queries () in
                              if uu____16242
                              then
                                let uu____16244 =
                                  let uu____16245 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____16246 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____16247 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16245 uu____16246 uu____16247 in
                                Some uu____16244
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (Some a_name), a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____16258,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____16267 = encode_free_var env1 fv t t_norm [] in
                 (match uu____16267 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____16280,se,uu____16282) ->
                 let uu____16285 = encode_sigelt env1 se in
                 (match uu____16285 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16295,se) ->
                 let uu____16299 = encode_sigelt env1 se in
                 (match uu____16299 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16309 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16309 with | (uu____16321,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____16369  ->
            match uu____16369 with
            | (l,uu____16376,uu____16377) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____16398  ->
            match uu____16398 with
            | (l,uu____16406,uu____16407) ->
                let uu____16412 =
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_SMTEncoding_Term.Echo _0_49) (
                    fst l) in
                let uu____16413 =
                  let uu____16415 =
                    let uu____16416 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____16416 in
                  [uu____16415] in
                uu____16412 :: uu____16413)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____16428 =
      let uu____16430 =
        let uu____16431 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____16433 =
          let uu____16434 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____16434 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____16431;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____16433
        } in
      [uu____16430] in
    FStar_ST.write last_env uu____16428
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____16446 = FStar_ST.read last_env in
      match uu____16446 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16452 ->
          let uu___153_16454 = e in
          let uu____16455 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_16454.bindings);
            depth = (uu___153_16454.depth);
            tcenv;
            warn = (uu___153_16454.warn);
            cache = (uu___153_16454.cache);
            nolabels = (uu___153_16454.nolabels);
            use_zfuel_name = (uu___153_16454.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_16454.encode_non_total_function_typ);
            current_module_name = uu____16455
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____16460 = FStar_ST.read last_env in
    match uu____16460 with
    | [] -> failwith "Empty env stack"
    | uu____16465::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____16474  ->
    let uu____16475 = FStar_ST.read last_env in
    match uu____16475 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_16486 = hd1 in
          {
            bindings = (uu___154_16486.bindings);
            depth = (uu___154_16486.depth);
            tcenv = (uu___154_16486.tcenv);
            warn = (uu___154_16486.warn);
            cache = refs;
            nolabels = (uu___154_16486.nolabels);
            use_zfuel_name = (uu___154_16486.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_16486.encode_non_total_function_typ);
            current_module_name = (uu___154_16486.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____16493  ->
    let uu____16494 = FStar_ST.read last_env in
    match uu____16494 with
    | [] -> failwith "Popping an empty stack"
    | uu____16499::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____16508  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____16512  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____16516  ->
    let uu____16517 = FStar_ST.read last_env in
    match uu____16517 with
    | hd1::uu____16523::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____16529 -> failwith "Impossible"
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
        | (uu____16588::uu____16589,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16593 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16593.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16593.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16593.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16594 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____16607 =
        let uu____16609 =
          let uu____16610 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____16610 in
        let uu____16611 = open_fact_db_tags env in uu____16609 :: uu____16611 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16607
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____16628 = encode_sigelt env se in
      match uu____16628 with
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
        let uu____16655 = FStar_Options.log_queries () in
        if uu____16655
        then
          let uu____16657 =
            let uu____16658 =
              let uu____16659 =
                let uu____16660 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16660 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____16659 in
            FStar_SMTEncoding_Term.Caption uu____16658 in
          uu____16657 :: decls
        else decls in
      let env =
        let uu____16667 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16667 tcenv in
      let uu____16668 = encode_top_level_facts env se in
      match uu____16668 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16677 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____16677))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____16690 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16690
       then
         let uu____16691 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16691
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16714  ->
                 fun se  ->
                   match uu____16714 with
                   | (g,env2) ->
                       let uu____16726 = encode_top_level_facts env2 se in
                       (match uu____16726 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16739 =
         encode_signature
           (let uu___156_16743 = env in
            {
              bindings = (uu___156_16743.bindings);
              depth = (uu___156_16743.depth);
              tcenv = (uu___156_16743.tcenv);
              warn = false;
              cache = (uu___156_16743.cache);
              nolabels = (uu___156_16743.nolabels);
              use_zfuel_name = (uu___156_16743.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16743.encode_non_total_function_typ);
              current_module_name = (uu___156_16743.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16739 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16755 = FStar_Options.log_queries () in
             if uu____16755
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_16760 = env1 in
               {
                 bindings = (uu___157_16760.bindings);
                 depth = (uu___157_16760.depth);
                 tcenv = (uu___157_16760.tcenv);
                 warn = true;
                 cache = (uu___157_16760.cache);
                 nolabels = (uu___157_16760.nolabels);
                 use_zfuel_name = (uu___157_16760.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16760.encode_non_total_function_typ);
                 current_module_name = (uu___157_16760.current_module_name)
               });
            (let uu____16762 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16762
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list*
          FStar_SMTEncoding_ErrorReporting.label Prims.list*
          FStar_SMTEncoding_Term.decl* FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____16800 =
           let uu____16801 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16801.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16800);
        (let env =
           let uu____16803 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16803 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16810 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16831 = aux rest in
                 (match uu____16831 with
                  | (out,rest1) ->
                      let t =
                        let uu____16849 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16849 with
                        | Some uu____16853 ->
                            let uu____16854 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16854
                              x.FStar_Syntax_Syntax.sort
                        | uu____16855 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16858 =
                        let uu____16860 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16861 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16861.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16861.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16860 :: out in
                      (uu____16858, rest1))
             | uu____16864 -> ([], bindings1) in
           let uu____16868 = aux bindings in
           match uu____16868 with
           | (closing,bindings1) ->
               let uu____16882 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16882, bindings1) in
         match uu____16810 with
         | (q1,bindings1) ->
             let uu____16895 =
               let uu____16898 =
                 FStar_List.filter
                   (fun uu___124_16900  ->
                      match uu___124_16900 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16901 ->
                          false
                      | uu____16905 -> true) bindings1 in
               encode_env_bindings env uu____16898 in
             (match uu____16895 with
              | (env_decls,env1) ->
                  ((let uu____16916 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16916
                    then
                      let uu____16917 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16917
                    else ());
                   (let uu____16919 = encode_formula q1 env1 in
                    match uu____16919 with
                    | (phi,qdecls) ->
                        let uu____16931 =
                          let uu____16934 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16934 phi in
                        (match uu____16931 with
                         | (labels,phi1) ->
                             let uu____16944 = encode_labels labels in
                             (match uu____16944 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16965 =
                                      let uu____16969 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16970 =
                                        varops.mk_unique "@query" in
                                      (uu____16969, (Some "query"),
                                        uu____16970) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16965 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16985 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16985 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16987 = encode_formula q env in
       match uu____16987 with
       | (f,uu____16991) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16993) -> true
             | uu____16996 -> false)))