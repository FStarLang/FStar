open Prims
let add_fuel x tl1 =
  let uu____19 = FStar_Options.unthrottle_inductives () in
  if uu____19 then tl1 else x :: tl1
let withenv c uu____47 = match uu____47 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___102_86  ->
       match uu___102_86 with
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
        let uu___126_158 = a in
        let uu____159 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____159;
          FStar_Syntax_Syntax.index =
            (uu___126_158.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_158.FStar_Syntax_Syntax.sort)
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
    let uu___127_860 = x in
    let uu____861 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____861;
      FStar_Syntax_Syntax.index = (uu___127_860.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_860.FStar_Syntax_Syntax.sort)
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
         (fun uu___103_1121  ->
            match uu___103_1121 with
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
           (fun uu___104_1138  ->
              match uu___104_1138 with
              | Binding_var (x,uu____1140) ->
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
        (let uu___128_1211 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1211.tcenv);
           warn = (uu___128_1211.warn);
           cache = (uu___128_1211.cache);
           nolabels = (uu___128_1211.nolabels);
           use_zfuel_name = (uu___128_1211.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1211.encode_non_total_function_typ);
           current_module_name = (uu___128_1211.current_module_name)
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
        (let uu___129_1226 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1226.depth);
           tcenv = (uu___129_1226.tcenv);
           warn = (uu___129_1226.warn);
           cache = (uu___129_1226.cache);
           nolabels = (uu___129_1226.nolabels);
           use_zfuel_name = (uu___129_1226.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1226.encode_non_total_function_typ);
           current_module_name = (uu___129_1226.current_module_name)
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
          (let uu___130_1245 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1245.depth);
             tcenv = (uu___130_1245.tcenv);
             warn = (uu___130_1245.warn);
             cache = (uu___130_1245.cache);
             nolabels = (uu___130_1245.nolabels);
             use_zfuel_name = (uu___130_1245.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1245.encode_non_total_function_typ);
             current_module_name = (uu___130_1245.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1258 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1258.depth);
          tcenv = (uu___131_1258.tcenv);
          warn = (uu___131_1258.warn);
          cache = (uu___131_1258.cache);
          nolabels = (uu___131_1258.nolabels);
          use_zfuel_name = (uu___131_1258.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1258.encode_non_total_function_typ);
          current_module_name = (uu___131_1258.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_1276  ->
             match uu___105_1276 with
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
      let uu____1324 =
        let uu___132_1325 = env in
        let uu____1326 =
          let uu____1328 =
            let uu____1329 =
              let uu____1336 =
                let uu____1338 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1338 in
              (x, fname, uu____1336, None) in
            Binding_fvar uu____1329 in
          uu____1328 :: (env.bindings) in
        {
          bindings = uu____1326;
          depth = (uu___132_1325.depth);
          tcenv = (uu___132_1325.tcenv);
          warn = (uu___132_1325.warn);
          cache = (uu___132_1325.cache);
          nolabels = (uu___132_1325.nolabels);
          use_zfuel_name = (uu___132_1325.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1325.encode_non_total_function_typ);
          current_module_name = (uu___132_1325.current_module_name)
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
        (fun uu___106_1362  ->
           match uu___106_1362 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1872 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1886 =
        lookup_binding env
          (fun uu___107_1400  ->
             match uu___107_1400 with
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
          let uu___133_1478 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1478.depth);
            tcenv = (uu___133_1478.tcenv);
            warn = (uu___133_1478.warn);
            cache = (uu___133_1478.cache);
            nolabels = (uu___133_1478.nolabels);
            use_zfuel_name = (uu___133_1478.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1478.encode_non_total_function_typ);
            current_module_name = (uu___133_1478.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1981 = lookup_lid env x in
        match uu____1981 with
        | (t1,t2,uu____1989) ->
            let t3 =
              let uu____1507 =
                let uu____1511 =
                  let uu____1513 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1513] in
                (f, uu____1511) in
              FStar_SMTEncoding_Util.mkApp uu____1507 in
            let uu___134_1516 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_1516.depth);
              tcenv = (uu___134_1516.tcenv);
              warn = (uu___134_1516.warn);
              cache = (uu___134_1516.cache);
              nolabels = (uu___134_1516.nolabels);
              use_zfuel_name = (uu___134_1516.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1516.encode_non_total_function_typ);
              current_module_name = (uu___134_1516.current_module_name)
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
        (fun uu___108_1707  ->
           match uu___108_1707 with
           | Binding_fvar (uu____1709,nm',tok,uu____1712) when nm = nm' ->
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
      | FStar_Syntax_Syntax.Tm_arrow uu____1826 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1834 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1839 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1840 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1849 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1859 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1861 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1861 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1875;
             FStar_Syntax_Syntax.pos = uu____1876;
             FStar_Syntax_Syntax.vars = uu____1877;_},uu____1878)
          ->
          let uu____1893 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1893 FStar_Option.isNone
      | uu____1906 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1915 =
        let uu____1916 = FStar_Syntax_Util.un_uinst t in
        uu____1916.FStar_Syntax_Syntax.n in
      match uu____1915 with
      | FStar_Syntax_Syntax.Tm_abs (uu____1919,uu____1920,Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Syntax_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_1933  ->
                  match uu___109_1933 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1934 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1936 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1936 FStar_Option.isSome
      | uu____1949 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1958 = head_normal env t in
      if uu____1958
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
    let uu____1972 =
      let uu____1973 = FStar_Syntax_Syntax.null_binder t in [uu____1973] in
    let uu____1974 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1972 uu____1974 None
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
                    let uu____1998 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1998
                | s ->
                    let uu____2001 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2001) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___110_2016  ->
    match uu___110_2016 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2017 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____2048;
                       FStar_SMTEncoding_Term.rng = uu____2049;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2063) ->
              let uu____2068 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2082 -> false) args (FStar_List.rev xs)) in
              if uu____2068 then tok_of_name env f else None
          | (uu____2085,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2088 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2090 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2090)) in
              if uu____2088 then Some t else None
          | uu____2093 -> None in
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
    | uu____2192 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2196  ->
    match uu___111_2196 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2198 =
          let uu____2202 =
            let uu____2204 =
              let uu____2205 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2205 in
            [uu____2204] in
          ("FStar.Char.Char", uu____2202) in
        FStar_SMTEncoding_Util.mkApp uu____2198
    | FStar_Const.Const_int (i,None ) ->
        let uu____2213 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2213
    | FStar_Const.Const_int (i,Some uu____2215) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2224) ->
        let uu____2227 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2227
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2231 =
          let uu____2232 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2232 in
        failwith uu____2231
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2253 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2261 ->
            let uu____2266 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2266
        | uu____2267 ->
            if norm1
            then let uu____2268 = whnf env t1 in aux false uu____2268
            else
              (let uu____2270 =
                 let uu____2271 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2272 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2271 uu____2272 in
               failwith uu____2270) in
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
    | uu____2294 ->
        let uu____2295 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2295)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2327::uu____2328::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2331::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2333 -> false
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
        (let uu____2471 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2471
         then
           let uu____2472 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2472
         else ());
        (let uu____2474 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2510  ->
                   fun b  ->
                     match uu____2510 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2553 =
                           let x = unmangle (fst b) in
                           let uu____2562 = gen_term_var env1 x in
                           match uu____2562 with
                           | (xxsym,xx,env') ->
                               let uu____2576 =
                                 let uu____2579 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2579 env1 xx in
                               (match uu____2576 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2553 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2474 with
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
          let uu____2667 = encode_term t env in
          match uu____2667 with
          | (t1,decls) ->
              let uu____2674 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2674, decls)
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
          let uu____2682 = encode_term t env in
          match uu____2682 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2691 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2691, decls)
               | Some f ->
                   let uu____2693 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2693, decls))
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
        let uu____2699 = encode_args args_e env in
        match uu____2699 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2711 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2718 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2718 in
            let binary arg_tms1 =
              let uu____2727 =
                let uu____2728 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2728 in
              let uu____2729 =
                let uu____2730 =
                  let uu____2731 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2731 in
                FStar_SMTEncoding_Term.unboxInt uu____2730 in
              (uu____2727, uu____2729) in
            let mk_default uu____2736 =
              let uu____2737 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2737 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2782 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2782
              then
                let uu____2783 = let uu____2784 = mk_args ts in op uu____2784 in
                FStar_All.pipe_right uu____2783 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2807 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2807
              then
                let uu____2808 = binary ts in
                match uu____2808 with
                | (t1,t2) ->
                    let uu____2813 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2813
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2816 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2816
                 then
                   let uu____2817 = op (binary ts) in
                   FStar_All.pipe_right uu____2817
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
            let uu____2907 =
              let uu____2913 =
                FStar_List.tryFind
                  (fun uu____2925  ->
                     match uu____2925 with
                     | (l,uu____2932) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2913 FStar_Util.must in
            (match uu____2907 with
             | (uu____2957,op) ->
                 let uu____2965 = op arg_tms in (uu____2965, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2972 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2972
       then
         let uu____2973 = FStar_Syntax_Print.tag_of_term t in
         let uu____2974 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2975 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2973 uu____2974
           uu____2975
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2979 ->
           let uu____2994 =
             let uu____2995 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2996 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2997 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2998 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2995
               uu____2996 uu____2997 uu____2998 in
           failwith uu____2994
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3001 =
             let uu____3002 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3003 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3004 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3005 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3002
               uu____3003 uu____3004 uu____3005 in
           failwith uu____3001
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3009 =
             let uu____3010 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3010 in
           failwith uu____3009
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3015) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3045) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3054 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3054, [])
       | FStar_Syntax_Syntax.Tm_type uu____3060 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3063) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3069 = encode_const c in (uu____3069, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3084 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3084 with
            | (binders1,res) ->
                let uu____3091 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3091
                then
                  let uu____3094 = encode_binders None binders1 env in
                  (match uu____3094 with
                   | (vars,guards,env',decls,uu____3109) ->
                       let fsym =
                         let uu____3119 = varops.fresh "f" in
                         (uu____3119, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3122 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3126 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3126.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3126.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3126.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3126.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3126.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3126.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3126.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3126.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3126.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3126.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3126.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3126.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3126.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3126.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3126.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3126.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3126.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3126.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3126.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3126.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3126.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3126.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3126.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_3126.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_3126.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_3126.FStar_TypeChecker_Env.is_native_tactic)
                            }) res in
                       (match uu____3122 with
                        | (pre_opt,res_t) ->
                            let uu____3133 =
                              encode_term_pred None res_t env' app in
                            (match uu____3133 with
                             | (res_pred,decls') ->
                                 let uu____3140 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3147 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3147, [])
                                   | Some pre ->
                                       let uu____3150 =
                                         encode_formula pre env' in
                                       (match uu____3150 with
                                        | (guard,decls0) ->
                                            let uu____3158 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3158, decls0)) in
                                 (match uu____3140 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3166 =
                                          let uu____3172 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3172) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3166 in
                                      let cvars =
                                        let uu____3182 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3182
                                          (FStar_List.filter
                                             (fun uu____3188  ->
                                                match uu____3188 with
                                                | (x,uu____3192) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3203 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3203 with
                                       | Some cache_entry ->
                                           let uu____3208 =
                                             let uu____3209 =
                                               let uu____3213 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3213) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3209 in
                                           (uu____3208,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3224 =
                                               let uu____3225 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3225 in
                                             varops.mk_unique uu____3224 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3232 =
                                               FStar_Options.log_queries () in
                                             if uu____3232
                                             then
                                               let uu____3234 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3234
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3240 =
                                               let uu____3244 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3244) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3240 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3252 =
                                               let uu____3256 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3256, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3252 in
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
                                             let uu____3269 =
                                               let uu____3273 =
                                                 let uu____3274 =
                                                   let uu____3280 =
                                                     let uu____3281 =
                                                       let uu____3284 =
                                                         let uu____3285 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3285 in
                                                       (f_has_t, uu____3284) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3281 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3280) in
                                                 mkForall_fuel uu____3274 in
                                               (uu____3273,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3269 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3298 =
                                               let uu____3302 =
                                                 let uu____3303 =
                                                   let uu____3309 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3309) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3303 in
                                               (uu____3302, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3298 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3323 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3323);
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
                     let uu____3334 =
                       let uu____3338 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3338, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3334 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3347 =
                       let uu____3351 =
                         let uu____3352 =
                           let uu____3358 =
                             let uu____3359 =
                               let uu____3362 =
                                 let uu____3363 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3363 in
                               (f_has_t, uu____3362) in
                             FStar_SMTEncoding_Util.mkImp uu____3359 in
                           ([[f_has_t]], [fsym], uu____3358) in
                         mkForall_fuel uu____3352 in
                       (uu____3351, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3347 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3377 ->
           let uu____3382 =
             let uu____3385 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3385 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3390;
                 FStar_Syntax_Syntax.pos = uu____3391;
                 FStar_Syntax_Syntax.vars = uu____3392;_} ->
                 let uu____3399 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3399 with
                  | (b,f1) ->
                      let uu____3413 =
                        let uu____3414 = FStar_List.hd b in fst uu____3414 in
                      (uu____3413, f1))
             | uu____3419 -> failwith "impossible" in
           (match uu____3382 with
            | (x,f) ->
                let uu____3426 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3426 with
                 | (base_t,decls) ->
                     let uu____3433 = gen_term_var env x in
                     (match uu____3433 with
                      | (x1,xtm,env') ->
                          let uu____3442 = encode_formula f env' in
                          (match uu____3442 with
                           | (refinement,decls') ->
                               let uu____3449 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3449 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3460 =
                                        let uu____3462 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3466 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3462
                                          uu____3466 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3460 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3482  ->
                                              match uu____3482 with
                                              | (y,uu____3486) ->
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
                                    let uu____3505 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3505 with
                                     | Some cache_entry ->
                                         let uu____3510 =
                                           let uu____3511 =
                                             let uu____3515 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3515) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3511 in
                                         (uu____3510,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3527 =
                                             let uu____3528 =
                                               let uu____3529 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3529 in
                                             Prims.strcat module_name
                                               uu____3528 in
                                           varops.mk_unique uu____3527 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3538 =
                                             let uu____3542 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3542) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3538 in
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
                                           let uu____3553 =
                                             let uu____3557 =
                                               let uu____3558 =
                                                 let uu____3564 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3564) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3558 in
                                             (uu____3557,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3553 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____3579 =
                                             let uu____3583 =
                                               let uu____3584 =
                                                 let uu____3590 =
                                                   let uu____3591 =
                                                     let uu____3594 =
                                                       let uu____3595 =
                                                         let uu____3601 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____3601) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____3595 in
                                                     (uu____3594, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____3591 in
                                                 ([[valid_t]], cvars1,
                                                   uu____3590) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3584 in
                                             (uu____3583,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3579 in
                                         let t_kinding =
                                           let uu____3621 =
                                             let uu____3625 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3625,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3621 in
                                         let t_interp =
                                           let uu____3635 =
                                             let uu____3639 =
                                               let uu____3640 =
                                                 let uu____3646 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3646) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3640 in
                                             let uu____3658 =
                                               let uu____3660 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3660 in
                                             (uu____3639, uu____3658,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3635 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3665 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3665);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3682 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3682 in
           let uu____3683 = encode_term_pred None k env ttm in
           (match uu____3683 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3691 =
                    let uu____3695 =
                      let uu____3696 =
                        let uu____3697 =
                          let uu____3698 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3698 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3697 in
                      varops.mk_unique uu____3696 in
                    (t_has_k, (Some "Uvar typing"), uu____3695) in
                  FStar_SMTEncoding_Util.mkAssume uu____3691 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3701 ->
           let uu____3711 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3711 with
            | (head1,args_e) ->
                let uu____3739 =
                  let uu____3747 =
                    let uu____3748 = FStar_Syntax_Subst.compress head1 in
                    uu____3748.FStar_Syntax_Syntax.n in
                  (uu____3747, args_e) in
                (match uu____3739 with
                 | uu____3758 when head_redex env head1 ->
                     let uu____3766 = whnf env t in
                     encode_term uu____3766 env
                 | uu____3767 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3780;
                       FStar_Syntax_Syntax.pos = uu____3781;
                       FStar_Syntax_Syntax.vars = uu____3782;_},uu____3783),uu____3784::
                    (v1,uu____3786)::(v2,uu____3788)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3826 = encode_term v1 env in
                     (match uu____3826 with
                      | (v11,decls1) ->
                          let uu____3833 = encode_term v2 env in
                          (match uu____3833 with
                           | (v21,decls2) ->
                               let uu____3840 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3840,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3843::(v1,uu____3845)::(v2,uu____3847)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3881 = encode_term v1 env in
                     (match uu____3881 with
                      | (v11,decls1) ->
                          let uu____3888 = encode_term v2 env in
                          (match uu____3888 with
                           | (v21,decls2) ->
                               let uu____3895 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3895,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3897) ->
                     let e0 =
                       let uu____3909 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3909 in
                     ((let uu____3915 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3915
                       then
                         let uu____3916 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3916
                       else ());
                      (let e =
                         let uu____3921 =
                           let uu____3922 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3923 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3922
                             uu____3923 in
                         uu____3921 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3932),(arg,uu____3934)::[]) -> encode_term arg env
                 | uu____3952 ->
                     let uu____3960 = encode_args args_e env in
                     (match uu____3960 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3993 = encode_term head1 env in
                            match uu____3993 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____4032 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4032 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4076  ->
                                                 fun uu____4077  ->
                                                   match (uu____4076,
                                                           uu____4077)
                                                   with
                                                   | ((bv,uu____4091),
                                                      (a,uu____4093)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4107 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4107
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4112 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____4112 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4122 =
                                                   let uu____4126 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4131 =
                                                     let uu____4132 =
                                                       let uu____4133 =
                                                         let uu____4134 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4134 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4133 in
                                                     varops.mk_unique
                                                       uu____4132 in
                                                   (uu____4126,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4131) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4122 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4151 = lookup_free_var_sym env fv in
                            match uu____4151 with
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
                                   FStar_Syntax_Syntax.tk = uu____4174;
                                   FStar_Syntax_Syntax.pos = uu____4175;
                                   FStar_Syntax_Syntax.vars = uu____4176;_},uu____4177)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4188;
                                   FStar_Syntax_Syntax.pos = uu____4189;
                                   FStar_Syntax_Syntax.vars = uu____4190;_},uu____4191)
                                ->
                                let uu____4196 =
                                  let uu____4197 =
                                    let uu____4200 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4200
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4197
                                    FStar_Pervasives.snd in
                                Some uu____4196
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4220 =
                                  let uu____4221 =
                                    let uu____4224 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4224
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4221
                                    FStar_Pervasives.snd in
                                Some uu____4220
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4243,(FStar_Util.Inl t1,uu____4245),uu____4246)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4284,(FStar_Util.Inr c,uu____4286),uu____4287)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4325 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4345 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4345 in
                               let uu____4346 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4346 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4356;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4357;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4358;_},uu____4359)
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
                                     | uu____4391 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4431 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4431 with
            | (bs1,body1,opening) ->
                let fallback uu____4446 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4451 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4451, [decl]) in
                let is_impure rc =
                  let uu____4457 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect in
                  FStar_All.pipe_right uu____4457 Prims.op_Negation in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | None  ->
                        let uu____4466 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4466 FStar_Pervasives.fst
                    | Some t1 -> t1 in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Syntax_Const.effect_Tot_lid
                  then
                    let uu____4479 = FStar_Syntax_Syntax.mk_Total res_typ in
                    Some uu____4479
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Syntax_Const.effect_GTot_lid
                    then
                      (let uu____4482 = FStar_Syntax_Syntax.mk_GTotal res_typ in
                       Some uu____4482)
                    else None in
                (match lopt with
                 | None  ->
                     ((let uu____4487 =
                         let uu____4488 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4488 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4487);
                      fallback ())
                 | Some rc ->
                     let uu____4490 =
                       (is_impure rc) &&
                         (let uu____4491 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc in
                          Prims.op_Negation uu____4491) in
                     if uu____4490
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4496 = encode_binders None bs1 env in
                        match uu____4496 with
                        | (vars,guards,envbody,decls,uu____4511) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1 in
                            let uu____4519 = encode_term body2 envbody in
                            (match uu____4519 with
                             | (body3,decls') ->
                                 let uu____4526 =
                                   let uu____4531 = codomain_eff rc in
                                   match uu____4531 with
                                   | None  -> (None, [])
                                   | Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c in
                                       let uu____4543 = encode_term tfun env in
                                       (match uu____4543 with
                                        | (t1,decls1) -> ((Some t1), decls1)) in
                                 (match uu____4526 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____4562 =
                                          let uu____4568 =
                                            let uu____4569 =
                                              let uu____4572 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards in
                                              (uu____4572, body3) in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____4569 in
                                          ([], vars, uu____4568) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____4562 in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | None  -> cvars
                                        | Some t1 ->
                                            let uu____4580 =
                                              let uu____4582 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1 in
                                              FStar_List.append uu____4582
                                                cvars in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____4580 in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____4593 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____4593 with
                                       | Some cache_entry ->
                                           let uu____4598 =
                                             let uu____4599 =
                                               let uu____4603 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1 in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____4603) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____4599 in
                                           (uu____4598,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let uu____4609 =
                                             is_an_eta_expansion env vars
                                               body3 in
                                           (match uu____4609 with
                                            | Some t1 ->
                                                let decls1 =
                                                  let uu____4616 =
                                                    let uu____4617 =
                                                      FStar_Util.smap_size
                                                        env.cache in
                                                    uu____4617 = cache_size in
                                                  if uu____4616
                                                  then []
                                                  else
                                                    FStar_List.append decls
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
                                                    let uu____4628 =
                                                      let uu____4629 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____4629 in
                                                    varops.mk_unique
                                                      uu____4628 in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym) in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None) in
                                                let f =
                                                  let uu____4634 =
                                                    let uu____4638 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    (fsym, uu____4638) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4634 in
                                                let app = mk_Apply f vars in
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
                                                      let uu____4650 =
                                                        let uu____4651 =
                                                          let uu____4655 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t) in
                                                          (uu____4655,
                                                            (Some a_name),
                                                            a_name) in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____4651 in
                                                      [uu____4650] in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym in
                                                  let uu____4663 =
                                                    let uu____4667 =
                                                      let uu____4668 =
                                                        let uu____4674 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3) in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____4674) in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____4668 in
                                                    (uu____4667,
                                                      (Some a_name), a_name) in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____4663 in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f]))) in
                                                ((let uu____4684 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____4684);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4686,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4687;
                          FStar_Syntax_Syntax.lbunivs = uu____4688;
                          FStar_Syntax_Syntax.lbtyp = uu____4689;
                          FStar_Syntax_Syntax.lbeff = uu____4690;
                          FStar_Syntax_Syntax.lbdef = uu____4691;_}::uu____4692),uu____4693)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4711;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4713;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4729 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4742 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4742, [decl_e])))
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
              let uu____4784 = encode_term e1 env in
              match uu____4784 with
              | (ee1,decls1) ->
                  let uu____4791 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4791 with
                   | (xs,e21) ->
                       let uu____4805 = FStar_List.hd xs in
                       (match uu____4805 with
                        | (x1,uu____4813) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4815 = encode_body e21 env' in
                            (match uu____4815 with
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
            let uu____4837 =
              let uu____4841 =
                let uu____4842 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4842 in
              gen_term_var env uu____4841 in
            match uu____4837 with
            | (scrsym,scr',env1) ->
                let uu____4852 = encode_term e env1 in
                (match uu____4852 with
                 | (scr,decls) ->
                     let uu____4859 =
                       let encode_branch b uu____4875 =
                         match uu____4875 with
                         | (else_case,decls1) ->
                             let uu____4886 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4886 with
                              | (p,w,br) ->
                                  let uu____4907 = encode_pat env1 p in
                                  (match uu____4907 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4927  ->
                                                   match uu____4927 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4932 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____4947 =
                                               encode_term w1 env2 in
                                             (match uu____4947 with
                                              | (w2,decls2) ->
                                                  let uu____4955 =
                                                    let uu____4956 =
                                                      let uu____4959 =
                                                        let uu____4960 =
                                                          let uu____4963 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4963) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4960 in
                                                      (guard, uu____4959) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4956 in
                                                  (uu____4955, decls2)) in
                                       (match uu____4932 with
                                        | (guard1,decls2) ->
                                            let uu____4971 =
                                              encode_br br env2 in
                                            (match uu____4971 with
                                             | (br1,decls3) ->
                                                 let uu____4979 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4979,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4859 with
                      | (match_tm,decls1) ->
                          let uu____4990 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4990, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5012 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5012
       then
         let uu____5013 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5013
       else ());
      (let uu____5015 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5015 with
       | (vars,pat_term) ->
           let uu____5025 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5048  ->
                     fun v1  ->
                       match uu____5048 with
                       | (env1,vars1) ->
                           let uu____5076 = gen_term_var env1 v1 in
                           (match uu____5076 with
                            | (xx,uu____5088,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5025 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5135 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5136 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5137 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5143 =
                        let uu____5146 = encode_const c in
                        (scrutinee, uu____5146) in
                      FStar_SMTEncoding_Util.mkEq uu____5143
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5165 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5165 with
                        | (uu____5169,uu____5170::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5172 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5193  ->
                                  match uu____5193 with
                                  | (arg,uu____5199) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5209 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5209)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5229) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5248 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5263 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5285  ->
                                  match uu____5285 with
                                  | (arg,uu____5294) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5304 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5304)) in
                      FStar_All.pipe_right uu____5263 FStar_List.flatten in
                let pat_term1 uu____5320 = encode_term pat_term env1 in
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
      let uu____5327 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5342  ->
                fun uu____5343  ->
                  match (uu____5342, uu____5343) with
                  | ((tms,decls),(t,uu____5363)) ->
                      let uu____5374 = encode_term t env in
                      (match uu____5374 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5327 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5408 = FStar_Syntax_Util.list_elements e in
        match uu____5408 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5423 =
          let uu____5433 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5433 FStar_Syntax_Util.head_and_args in
        match uu____5423 with
        | (head1,args) ->
            let uu____5461 =
              let uu____5469 =
                let uu____5470 = FStar_Syntax_Util.un_uinst head1 in
                uu____5470.FStar_Syntax_Syntax.n in
              (uu____5469, args) in
            (match uu____5461 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5481,uu____5482)::(e,uu____5484)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____5510 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____5537 =
            let uu____5547 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5547 FStar_Syntax_Util.head_and_args in
          match uu____5537 with
          | (head1,args) ->
              let uu____5576 =
                let uu____5584 =
                  let uu____5585 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5585.FStar_Syntax_Syntax.n in
                (uu____5584, args) in
              (match uu____5576 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5598)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5618 -> None) in
        match elts with
        | t1::[] ->
            let uu____5633 = smt_pat_or1 t1 in
            (match uu____5633 with
             | Some e ->
                 let uu____5646 = list_elements1 e in
                 FStar_All.pipe_right uu____5646
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5657 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5657
                           (FStar_List.map one_pat)))
             | uu____5665 ->
                 let uu____5669 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5669])
        | uu____5685 ->
            let uu____5687 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5687] in
      let uu____5703 =
        let uu____5716 =
          let uu____5717 = FStar_Syntax_Subst.compress t in
          uu____5717.FStar_Syntax_Syntax.n in
        match uu____5716 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5744 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5744 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5773;
                        FStar_Syntax_Syntax.effect_name = uu____5774;
                        FStar_Syntax_Syntax.result_typ = uu____5775;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5777)::(post,uu____5779)::(pats,uu____5781)::[];
                        FStar_Syntax_Syntax.flags = uu____5782;_}
                      ->
                      let uu____5814 = lemma_pats pats in
                      (binders1, pre, post, uu____5814)
                  | uu____5827 -> failwith "impos"))
        | uu____5840 -> failwith "Impos" in
      match uu____5703 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_5876 = env in
            {
              bindings = (uu___136_5876.bindings);
              depth = (uu___136_5876.depth);
              tcenv = (uu___136_5876.tcenv);
              warn = (uu___136_5876.warn);
              cache = (uu___136_5876.cache);
              nolabels = (uu___136_5876.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_5876.encode_non_total_function_typ);
              current_module_name = (uu___136_5876.current_module_name)
            } in
          let uu____5877 = encode_binders None binders env1 in
          (match uu____5877 with
           | (vars,guards,env2,decls,uu____5892) ->
               let uu____5899 =
                 let uu____5906 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5928 =
                             let uu____5933 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5933 FStar_List.unzip in
                           match uu____5928 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5906 FStar_List.unzip in
               (match uu____5899 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_5991 = env2 in
                      {
                        bindings = (uu___137_5991.bindings);
                        depth = (uu___137_5991.depth);
                        tcenv = (uu___137_5991.tcenv);
                        warn = (uu___137_5991.warn);
                        cache = (uu___137_5991.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_5991.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_5991.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_5991.current_module_name)
                      } in
                    let uu____5992 =
                      let uu____5995 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5995 env3 in
                    (match uu____5992 with
                     | (pre1,decls'') ->
                         let uu____6000 =
                           let uu____6003 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6003 env3 in
                         (match uu____6000 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6010 =
                                let uu____6011 =
                                  let uu____6017 =
                                    let uu____6018 =
                                      let uu____6021 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6021, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6018 in
                                  (pats, vars, uu____6017) in
                                FStar_SMTEncoding_Util.mkForall uu____6011 in
                              (uu____6010, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6034 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6034
        then
          let uu____6035 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6036 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6035 uu____6036
        else () in
      let enc f r l =
        let uu____6063 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6076 = encode_term (fst x) env in
                 match uu____6076 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6063 with
        | (decls,args) ->
            let uu____6093 =
              let uu___138_6094 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6094.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6094.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6093, decls) in
      let const_op f r uu____6119 = let uu____6128 = f r in (uu____6128, []) in
      let un_op f l =
        let uu____6144 = FStar_List.hd l in FStar_All.pipe_left f uu____6144 in
      let bin_op f uu___112_6157 =
        match uu___112_6157 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6165 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6192 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6201  ->
                 match uu____6201 with
                 | (t,uu____6209) ->
                     let uu____6210 = encode_formula t env in
                     (match uu____6210 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6192 with
        | (decls,phis) ->
            let uu____6227 =
              let uu___139_6228 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6228.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6228.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6227, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6267  ->
               match uu____6267 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6281) -> false
                    | uu____6282 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6295 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6295
        else
          (let uu____6310 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6310 r rf) in
      let mk_imp1 r uu___113_6329 =
        match uu___113_6329 with
        | (lhs,uu____6333)::(rhs,uu____6335)::[] ->
            let uu____6356 = encode_formula rhs env in
            (match uu____6356 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6365) ->
                      (l1, decls1)
                  | uu____6368 ->
                      let uu____6369 = encode_formula lhs env in
                      (match uu____6369 with
                       | (l2,decls2) ->
                           let uu____6376 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6376, (FStar_List.append decls1 decls2)))))
        | uu____6378 -> failwith "impossible" in
      let mk_ite r uu___114_6393 =
        match uu___114_6393 with
        | (guard,uu____6397)::(_then,uu____6399)::(_else,uu____6401)::[] ->
            let uu____6430 = encode_formula guard env in
            (match uu____6430 with
             | (g,decls1) ->
                 let uu____6437 = encode_formula _then env in
                 (match uu____6437 with
                  | (t,decls2) ->
                      let uu____6444 = encode_formula _else env in
                      (match uu____6444 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6453 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6472 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6472 in
      let connectives =
        let uu____6484 =
          let uu____6493 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6493) in
        let uu____6506 =
          let uu____6516 =
            let uu____6525 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6525) in
          let uu____6538 =
            let uu____6548 =
              let uu____6558 =
                let uu____6567 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6567) in
              let uu____6580 =
                let uu____6590 =
                  let uu____6600 =
                    let uu____6609 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6609) in
                  [uu____6600;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6590 in
              uu____6558 :: uu____6580 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6548 in
          uu____6516 :: uu____6538 in
        uu____6484 :: uu____6506 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6825 = encode_formula phi' env in
            (match uu____6825 with
             | (phi2,decls) ->
                 let uu____6832 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6832, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6833 ->
            let uu____6838 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6838 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6867 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6867 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6875;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6877;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6893 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6893 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6925::(x,uu____6927)::(t,uu____6929)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6963 = encode_term x env in
                 (match uu____6963 with
                  | (x1,decls) ->
                      let uu____6970 = encode_term t env in
                      (match uu____6970 with
                       | (t1,decls') ->
                           let uu____6977 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6977, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6981)::(msg,uu____6983)::(phi2,uu____6985)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7019 =
                   let uu____7022 =
                     let uu____7023 = FStar_Syntax_Subst.compress r in
                     uu____7023.FStar_Syntax_Syntax.n in
                   let uu____7026 =
                     let uu____7027 = FStar_Syntax_Subst.compress msg in
                     uu____7027.FStar_Syntax_Syntax.n in
                   (uu____7022, uu____7026) in
                 (match uu____7019 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7034))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7050 -> fallback phi2)
             | uu____7053 when head_redex env head2 ->
                 let uu____7061 = whnf env phi1 in
                 encode_formula uu____7061 env
             | uu____7062 ->
                 let uu____7070 = encode_term phi1 env in
                 (match uu____7070 with
                  | (tt,decls) ->
                      let uu____7077 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7078 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7078.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7078.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7077, decls)))
        | uu____7081 ->
            let uu____7082 = encode_term phi1 env in
            (match uu____7082 with
             | (tt,decls) ->
                 let uu____7089 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7090 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7090.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7090.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7089, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7117 = encode_binders None bs env1 in
        match uu____7117 with
        | (vars,guards,env2,decls,uu____7139) ->
            let uu____7146 =
              let uu____7153 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7176 =
                          let uu____7181 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7195  ->
                                    match uu____7195 with
                                    | (t,uu____7201) ->
                                        encode_term t
                                          (let uu___142_7202 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7202.bindings);
                                             depth = (uu___142_7202.depth);
                                             tcenv = (uu___142_7202.tcenv);
                                             warn = (uu___142_7202.warn);
                                             cache = (uu___142_7202.cache);
                                             nolabels =
                                               (uu___142_7202.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7202.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7202.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7181 FStar_List.unzip in
                        match uu____7176 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7153 FStar_List.unzip in
            (match uu____7146 with
             | (pats,decls') ->
                 let uu____7254 = encode_formula body env2 in
                 (match uu____7254 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7273;
                             FStar_SMTEncoding_Term.rng = uu____7274;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7282 -> guards in
                      let uu____7285 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7285, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7319  ->
                   match uu____7319 with
                   | (x,uu____7323) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7329 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7335 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7335) uu____7329 tl1 in
             let uu____7337 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7349  ->
                       match uu____7349 with
                       | (b,uu____7353) ->
                           let uu____7354 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7354)) in
             (match uu____7337 with
              | None  -> ()
              | Some (x,uu____7358) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7368 =
                    let uu____7369 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7369 in
                  FStar_Errors.warn pos uu____7368) in
       let uu____7370 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7370 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7376 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7412  ->
                     match uu____7412 with
                     | (l,uu____7422) -> FStar_Ident.lid_equals op l)) in
           (match uu____7376 with
            | None  -> fallback phi1
            | Some (uu____7445,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7474 = encode_q_body env vars pats body in
             match uu____7474 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7500 =
                     let uu____7506 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7506) in
                   FStar_SMTEncoding_Term.mkForall uu____7500
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7518 = encode_q_body env vars pats body in
             match uu____7518 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7543 =
                   let uu____7544 =
                     let uu____7550 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7550) in
                   FStar_SMTEncoding_Term.mkExists uu____7544
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7543, decls))))
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
  let uu____7609 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7609 with
  | (asym,a) ->
      let uu____7614 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7614 with
       | (xsym,x) ->
           let uu____7619 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7619 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7649 =
                      let uu____7655 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7655, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7649 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7670 =
                      let uu____7674 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7674) in
                    FStar_SMTEncoding_Util.mkApp uu____7670 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7682 =
                    let uu____7684 =
                      let uu____7686 =
                        let uu____7688 =
                          let uu____7689 =
                            let uu____7693 =
                              let uu____7694 =
                                let uu____7700 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7700) in
                              FStar_SMTEncoding_Util.mkForall uu____7694 in
                            (uu____7693, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7689 in
                        let uu____7709 =
                          let uu____7711 =
                            let uu____7712 =
                              let uu____7716 =
                                let uu____7717 =
                                  let uu____7723 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7723) in
                                FStar_SMTEncoding_Util.mkForall uu____7717 in
                              (uu____7716,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7712 in
                          [uu____7711] in
                        uu____7688 :: uu____7709 in
                      xtok_decl :: uu____7686 in
                    xname_decl :: uu____7684 in
                  (xtok1, uu____7682) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7772 =
                    let uu____7780 =
                      let uu____7786 =
                        let uu____7787 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7787 in
                      quant axy uu____7786 in
                    (FStar_Syntax_Const.op_Eq, uu____7780) in
                  let uu____7793 =
                    let uu____7802 =
                      let uu____7810 =
                        let uu____7816 =
                          let uu____7817 =
                            let uu____7818 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7818 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7817 in
                        quant axy uu____7816 in
                      (FStar_Syntax_Const.op_notEq, uu____7810) in
                    let uu____7824 =
                      let uu____7833 =
                        let uu____7841 =
                          let uu____7847 =
                            let uu____7848 =
                              let uu____7849 =
                                let uu____7852 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7853 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7852, uu____7853) in
                              FStar_SMTEncoding_Util.mkLT uu____7849 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7848 in
                          quant xy uu____7847 in
                        (FStar_Syntax_Const.op_LT, uu____7841) in
                      let uu____7859 =
                        let uu____7868 =
                          let uu____7876 =
                            let uu____7882 =
                              let uu____7883 =
                                let uu____7884 =
                                  let uu____7887 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7888 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7887, uu____7888) in
                                FStar_SMTEncoding_Util.mkLTE uu____7884 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7883 in
                            quant xy uu____7882 in
                          (FStar_Syntax_Const.op_LTE, uu____7876) in
                        let uu____7894 =
                          let uu____7903 =
                            let uu____7911 =
                              let uu____7917 =
                                let uu____7918 =
                                  let uu____7919 =
                                    let uu____7922 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7923 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7922, uu____7923) in
                                  FStar_SMTEncoding_Util.mkGT uu____7919 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7918 in
                              quant xy uu____7917 in
                            (FStar_Syntax_Const.op_GT, uu____7911) in
                          let uu____7929 =
                            let uu____7938 =
                              let uu____7946 =
                                let uu____7952 =
                                  let uu____7953 =
                                    let uu____7954 =
                                      let uu____7957 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7958 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7957, uu____7958) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7954 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7953 in
                                quant xy uu____7952 in
                              (FStar_Syntax_Const.op_GTE, uu____7946) in
                            let uu____7964 =
                              let uu____7973 =
                                let uu____7981 =
                                  let uu____7987 =
                                    let uu____7988 =
                                      let uu____7989 =
                                        let uu____7992 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7993 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7992, uu____7993) in
                                      FStar_SMTEncoding_Util.mkSub uu____7989 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7988 in
                                  quant xy uu____7987 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7981) in
                              let uu____7999 =
                                let uu____8008 =
                                  let uu____8016 =
                                    let uu____8022 =
                                      let uu____8023 =
                                        let uu____8024 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8024 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8023 in
                                    quant qx uu____8022 in
                                  (FStar_Syntax_Const.op_Minus, uu____8016) in
                                let uu____8030 =
                                  let uu____8039 =
                                    let uu____8047 =
                                      let uu____8053 =
                                        let uu____8054 =
                                          let uu____8055 =
                                            let uu____8058 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8059 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8058, uu____8059) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8055 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8054 in
                                      quant xy uu____8053 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8047) in
                                  let uu____8065 =
                                    let uu____8074 =
                                      let uu____8082 =
                                        let uu____8088 =
                                          let uu____8089 =
                                            let uu____8090 =
                                              let uu____8093 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8094 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8093, uu____8094) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8090 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8089 in
                                        quant xy uu____8088 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8082) in
                                    let uu____8100 =
                                      let uu____8109 =
                                        let uu____8117 =
                                          let uu____8123 =
                                            let uu____8124 =
                                              let uu____8125 =
                                                let uu____8128 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8129 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8128, uu____8129) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8125 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8124 in
                                          quant xy uu____8123 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8117) in
                                      let uu____8135 =
                                        let uu____8144 =
                                          let uu____8152 =
                                            let uu____8158 =
                                              let uu____8159 =
                                                let uu____8160 =
                                                  let uu____8163 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8164 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8163, uu____8164) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8160 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8159 in
                                            quant xy uu____8158 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8152) in
                                        let uu____8170 =
                                          let uu____8179 =
                                            let uu____8187 =
                                              let uu____8193 =
                                                let uu____8194 =
                                                  let uu____8195 =
                                                    let uu____8198 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8199 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8198, uu____8199) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8195 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8194 in
                                              quant xy uu____8193 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8187) in
                                          let uu____8205 =
                                            let uu____8214 =
                                              let uu____8222 =
                                                let uu____8228 =
                                                  let uu____8229 =
                                                    let uu____8230 =
                                                      let uu____8233 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8234 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8233,
                                                        uu____8234) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8230 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8229 in
                                                quant xy uu____8228 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8222) in
                                            let uu____8240 =
                                              let uu____8249 =
                                                let uu____8257 =
                                                  let uu____8263 =
                                                    let uu____8264 =
                                                      let uu____8265 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8265 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8264 in
                                                  quant qx uu____8263 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8257) in
                                              [uu____8249] in
                                            uu____8214 :: uu____8240 in
                                          uu____8179 :: uu____8205 in
                                        uu____8144 :: uu____8170 in
                                      uu____8109 :: uu____8135 in
                                    uu____8074 :: uu____8100 in
                                  uu____8039 :: uu____8065 in
                                uu____8008 :: uu____8030 in
                              uu____7973 :: uu____7999 in
                            uu____7938 :: uu____7964 in
                          uu____7903 :: uu____7929 in
                        uu____7868 :: uu____7894 in
                      uu____7833 :: uu____7859 in
                    uu____7802 :: uu____7824 in
                  uu____7772 :: uu____7793 in
                let mk1 l v1 =
                  let uu____8393 =
                    let uu____8398 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8430  ->
                              match uu____8430 with
                              | (l',uu____8439) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8398
                      (FStar_Option.map
                         (fun uu____8472  ->
                            match uu____8472 with | (uu____8483,b) -> b v1)) in
                  FStar_All.pipe_right uu____8393 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8524  ->
                          match uu____8524 with
                          | (l',uu____8533) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8562 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8562 with
        | (xxsym,xx) ->
            let uu____8567 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8567 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8575 =
                   let uu____8579 =
                     let uu____8580 =
                       let uu____8586 =
                         let uu____8587 =
                           let uu____8590 =
                             let uu____8591 =
                               let uu____8594 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8594) in
                             FStar_SMTEncoding_Util.mkEq uu____8591 in
                           (xx_has_type, uu____8590) in
                         FStar_SMTEncoding_Util.mkImp uu____8587 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8586) in
                     FStar_SMTEncoding_Util.mkForall uu____8580 in
                   let uu____8607 =
                     let uu____8608 =
                       let uu____8609 =
                         let uu____8610 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8610 in
                       Prims.strcat module_name uu____8609 in
                     varops.mk_unique uu____8608 in
                   (uu____8579, (Some "pretyping"), uu____8607) in
                 FStar_SMTEncoding_Util.mkAssume uu____8575)
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
    let uu____8644 =
      let uu____8645 =
        let uu____8649 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8649, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8645 in
    let uu____8651 =
      let uu____8653 =
        let uu____8654 =
          let uu____8658 =
            let uu____8659 =
              let uu____8665 =
                let uu____8666 =
                  let uu____8669 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8669) in
                FStar_SMTEncoding_Util.mkImp uu____8666 in
              ([[typing_pred]], [xx], uu____8665) in
            mkForall_fuel uu____8659 in
          (uu____8658, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8654 in
      [uu____8653] in
    uu____8644 :: uu____8651 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8697 =
      let uu____8698 =
        let uu____8702 =
          let uu____8703 =
            let uu____8709 =
              let uu____8712 =
                let uu____8714 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8714] in
              [uu____8712] in
            let uu____8717 =
              let uu____8718 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8718 tt in
            (uu____8709, [bb], uu____8717) in
          FStar_SMTEncoding_Util.mkForall uu____8703 in
        (uu____8702, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8698 in
    let uu____8729 =
      let uu____8731 =
        let uu____8732 =
          let uu____8736 =
            let uu____8737 =
              let uu____8743 =
                let uu____8744 =
                  let uu____8747 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8747) in
                FStar_SMTEncoding_Util.mkImp uu____8744 in
              ([[typing_pred]], [xx], uu____8743) in
            mkForall_fuel uu____8737 in
          (uu____8736, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8732 in
      [uu____8731] in
    uu____8697 :: uu____8729 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8781 =
        let uu____8782 =
          let uu____8786 =
            let uu____8788 =
              let uu____8790 =
                let uu____8792 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8793 =
                  let uu____8795 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8795] in
                uu____8792 :: uu____8793 in
              tt :: uu____8790 in
            tt :: uu____8788 in
          ("Prims.Precedes", uu____8786) in
        FStar_SMTEncoding_Util.mkApp uu____8782 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8781 in
    let precedes_y_x =
      let uu____8798 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8798 in
    let uu____8800 =
      let uu____8801 =
        let uu____8805 =
          let uu____8806 =
            let uu____8812 =
              let uu____8815 =
                let uu____8817 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8817] in
              [uu____8815] in
            let uu____8820 =
              let uu____8821 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8821 tt in
            (uu____8812, [bb], uu____8820) in
          FStar_SMTEncoding_Util.mkForall uu____8806 in
        (uu____8805, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8801 in
    let uu____8832 =
      let uu____8834 =
        let uu____8835 =
          let uu____8839 =
            let uu____8840 =
              let uu____8846 =
                let uu____8847 =
                  let uu____8850 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8850) in
                FStar_SMTEncoding_Util.mkImp uu____8847 in
              ([[typing_pred]], [xx], uu____8846) in
            mkForall_fuel uu____8840 in
          (uu____8839, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8835 in
      let uu____8863 =
        let uu____8865 =
          let uu____8866 =
            let uu____8870 =
              let uu____8871 =
                let uu____8877 =
                  let uu____8878 =
                    let uu____8881 =
                      let uu____8882 =
                        let uu____8884 =
                          let uu____8886 =
                            let uu____8888 =
                              let uu____8889 =
                                let uu____8892 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8893 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8892, uu____8893) in
                              FStar_SMTEncoding_Util.mkGT uu____8889 in
                            let uu____8894 =
                              let uu____8896 =
                                let uu____8897 =
                                  let uu____8900 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8901 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8900, uu____8901) in
                                FStar_SMTEncoding_Util.mkGTE uu____8897 in
                              let uu____8902 =
                                let uu____8904 =
                                  let uu____8905 =
                                    let uu____8908 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8909 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8908, uu____8909) in
                                  FStar_SMTEncoding_Util.mkLT uu____8905 in
                                [uu____8904] in
                              uu____8896 :: uu____8902 in
                            uu____8888 :: uu____8894 in
                          typing_pred_y :: uu____8886 in
                        typing_pred :: uu____8884 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8882 in
                    (uu____8881, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8878 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8877) in
              mkForall_fuel uu____8871 in
            (uu____8870, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8866 in
        [uu____8865] in
      uu____8834 :: uu____8863 in
    uu____8800 :: uu____8832 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8939 =
      let uu____8940 =
        let uu____8944 =
          let uu____8945 =
            let uu____8951 =
              let uu____8954 =
                let uu____8956 = FStar_SMTEncoding_Term.boxString b in
                [uu____8956] in
              [uu____8954] in
            let uu____8959 =
              let uu____8960 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8960 tt in
            (uu____8951, [bb], uu____8959) in
          FStar_SMTEncoding_Util.mkForall uu____8945 in
        (uu____8944, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8940 in
    let uu____8971 =
      let uu____8973 =
        let uu____8974 =
          let uu____8978 =
            let uu____8979 =
              let uu____8985 =
                let uu____8986 =
                  let uu____8989 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8989) in
                FStar_SMTEncoding_Util.mkImp uu____8986 in
              ([[typing_pred]], [xx], uu____8985) in
            mkForall_fuel uu____8979 in
          (uu____8978, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8974 in
      [uu____8973] in
    uu____8939 :: uu____8971 in
  let mk_ref1 env reft_name uu____9011 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9022 =
        let uu____9026 =
          let uu____9028 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9028] in
        (reft_name, uu____9026) in
      FStar_SMTEncoding_Util.mkApp uu____9022 in
    let refb =
      let uu____9031 =
        let uu____9035 =
          let uu____9037 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9037] in
        (reft_name, uu____9035) in
      FStar_SMTEncoding_Util.mkApp uu____9031 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9041 =
      let uu____9042 =
        let uu____9046 =
          let uu____9047 =
            let uu____9053 =
              let uu____9054 =
                let uu____9057 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9057) in
              FStar_SMTEncoding_Util.mkImp uu____9054 in
            ([[typing_pred]], [xx; aa], uu____9053) in
          mkForall_fuel uu____9047 in
        (uu____9046, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9042 in
    [uu____9041] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9097 =
      let uu____9098 =
        let uu____9102 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9102, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9098 in
    [uu____9097] in
  let mk_and_interp env conj uu____9113 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9130 =
      let uu____9131 =
        let uu____9135 =
          let uu____9136 =
            let uu____9142 =
              let uu____9143 =
                let uu____9146 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9146, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9143 in
            ([[l_and_a_b]], [aa; bb], uu____9142) in
          FStar_SMTEncoding_Util.mkForall uu____9136 in
        (uu____9135, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9131 in
    [uu____9130] in
  let mk_or_interp env disj uu____9170 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9187 =
      let uu____9188 =
        let uu____9192 =
          let uu____9193 =
            let uu____9199 =
              let uu____9200 =
                let uu____9203 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9203, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9200 in
            ([[l_or_a_b]], [aa; bb], uu____9199) in
          FStar_SMTEncoding_Util.mkForall uu____9193 in
        (uu____9192, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9188 in
    [uu____9187] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9244 =
      let uu____9245 =
        let uu____9249 =
          let uu____9250 =
            let uu____9256 =
              let uu____9257 =
                let uu____9260 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9260, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9257 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9256) in
          FStar_SMTEncoding_Util.mkForall uu____9250 in
        (uu____9249, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9245 in
    [uu____9244] in
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
    let uu____9307 =
      let uu____9308 =
        let uu____9312 =
          let uu____9313 =
            let uu____9319 =
              let uu____9320 =
                let uu____9323 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9323, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9320 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9319) in
          FStar_SMTEncoding_Util.mkForall uu____9313 in
        (uu____9312, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9308 in
    [uu____9307] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9368 =
      let uu____9369 =
        let uu____9373 =
          let uu____9374 =
            let uu____9380 =
              let uu____9381 =
                let uu____9384 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9384, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9381 in
            ([[l_imp_a_b]], [aa; bb], uu____9380) in
          FStar_SMTEncoding_Util.mkForall uu____9374 in
        (uu____9373, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9369 in
    [uu____9368] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9425 =
      let uu____9426 =
        let uu____9430 =
          let uu____9431 =
            let uu____9437 =
              let uu____9438 =
                let uu____9441 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9441, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9438 in
            ([[l_iff_a_b]], [aa; bb], uu____9437) in
          FStar_SMTEncoding_Util.mkForall uu____9431 in
        (uu____9430, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9426 in
    [uu____9425] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9475 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9475 in
    let uu____9477 =
      let uu____9478 =
        let uu____9482 =
          let uu____9483 =
            let uu____9489 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9489) in
          FStar_SMTEncoding_Util.mkForall uu____9483 in
        (uu____9482, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9478 in
    [uu____9477] in
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
      let uu____9529 =
        let uu____9533 =
          let uu____9535 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9535] in
        ("Valid", uu____9533) in
      FStar_SMTEncoding_Util.mkApp uu____9529 in
    let uu____9537 =
      let uu____9538 =
        let uu____9542 =
          let uu____9543 =
            let uu____9549 =
              let uu____9550 =
                let uu____9553 =
                  let uu____9554 =
                    let uu____9560 =
                      let uu____9563 =
                        let uu____9565 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9565] in
                      [uu____9563] in
                    let uu____9568 =
                      let uu____9569 =
                        let uu____9572 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9572, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9569 in
                    (uu____9560, [xx1], uu____9568) in
                  FStar_SMTEncoding_Util.mkForall uu____9554 in
                (uu____9553, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9550 in
            ([[l_forall_a_b]], [aa; bb], uu____9549) in
          FStar_SMTEncoding_Util.mkForall uu____9543 in
        (uu____9542, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9538 in
    [uu____9537] in
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
      let uu____9623 =
        let uu____9627 =
          let uu____9629 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9629] in
        ("Valid", uu____9627) in
      FStar_SMTEncoding_Util.mkApp uu____9623 in
    let uu____9631 =
      let uu____9632 =
        let uu____9636 =
          let uu____9637 =
            let uu____9643 =
              let uu____9644 =
                let uu____9647 =
                  let uu____9648 =
                    let uu____9654 =
                      let uu____9657 =
                        let uu____9659 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9659] in
                      [uu____9657] in
                    let uu____9662 =
                      let uu____9663 =
                        let uu____9666 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9666, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9663 in
                    (uu____9654, [xx1], uu____9662) in
                  FStar_SMTEncoding_Util.mkExists uu____9648 in
                (uu____9647, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9644 in
            ([[l_exists_a_b]], [aa; bb], uu____9643) in
          FStar_SMTEncoding_Util.mkForall uu____9637 in
        (uu____9636, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9632 in
    [uu____9631] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9702 =
      let uu____9703 =
        let uu____9707 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9708 = varops.mk_unique "typing_range_const" in
        (uu____9707, (Some "Range_const typing"), uu____9708) in
      FStar_SMTEncoding_Util.mkAssume uu____9703 in
    [uu____9702] in
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
          let uu____9970 =
            FStar_Util.find_opt
              (fun uu____9988  ->
                 match uu____9988 with
                 | (l,uu____9998) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9970 with
          | None  -> []
          | Some (uu____10020,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10060 = encode_function_type_as_formula t env in
        match uu____10060 with
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
            let uu____10097 =
              (let uu____10098 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10098) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10097
            then
              let uu____10102 = new_term_constant_and_tok_from_lid env lid in
              match uu____10102 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10114 =
                      let uu____10115 = FStar_Syntax_Subst.compress t_norm in
                      uu____10115.FStar_Syntax_Syntax.n in
                    match uu____10114 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10120) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10137  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10140 -> [] in
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
              (let uu____10149 = prims.is lid in
               if uu____10149
               then
                 let vname = varops.new_fvar lid in
                 let uu____10154 = prims.mk lid vname in
                 match uu____10154 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10169 =
                    let uu____10175 = curried_arrow_formals_comp t_norm in
                    match uu____10175 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10186 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10186
                          then
                            let uu____10187 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10188 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10188.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10188.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10188.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10188.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10188.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10188.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10188.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10188.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10188.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10188.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10188.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10188.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10188.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10188.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10188.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10188.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10188.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10188.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10188.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10188.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10188.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10188.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10188.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10188.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10188.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10188.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10187
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10195 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10195)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10169 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10222 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10222 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10235 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10259  ->
                                     match uu___115_10259 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10262 =
                                           FStar_Util.prefix vars in
                                         (match uu____10262 with
                                          | (uu____10273,(xxsym,uu____10275))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10285 =
                                                let uu____10286 =
                                                  let uu____10290 =
                                                    let uu____10291 =
                                                      let uu____10297 =
                                                        let uu____10298 =
                                                          let uu____10301 =
                                                            let uu____10302 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10302 in
                                                          (vapp, uu____10301) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10298 in
                                                      ([[vapp]], vars,
                                                        uu____10297) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10291 in
                                                  (uu____10290,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10286 in
                                              [uu____10285])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10313 =
                                           FStar_Util.prefix vars in
                                         (match uu____10313 with
                                          | (uu____10324,(xxsym,uu____10326))
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
                                              let uu____10340 =
                                                let uu____10341 =
                                                  let uu____10345 =
                                                    let uu____10346 =
                                                      let uu____10352 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10352) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10346 in
                                                  (uu____10345,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10341 in
                                              [uu____10340])
                                     | uu____10361 -> [])) in
                           let uu____10362 = encode_binders None formals env1 in
                           (match uu____10362 with
                            | (vars,guards,env',decls1,uu____10378) ->
                                let uu____10385 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10390 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10390, decls1)
                                  | Some p ->
                                      let uu____10392 = encode_formula p env' in
                                      (match uu____10392 with
                                       | (g,ds) ->
                                           let uu____10399 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10399,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10385 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10408 =
                                         let uu____10412 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10412) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10408 in
                                     let uu____10417 =
                                       let vname_decl =
                                         let uu____10422 =
                                           let uu____10428 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10433  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10428,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10422 in
                                       let uu____10438 =
                                         let env2 =
                                           let uu___144_10442 = env1 in
                                           {
                                             bindings =
                                               (uu___144_10442.bindings);
                                             depth = (uu___144_10442.depth);
                                             tcenv = (uu___144_10442.tcenv);
                                             warn = (uu___144_10442.warn);
                                             cache = (uu___144_10442.cache);
                                             nolabels =
                                               (uu___144_10442.nolabels);
                                             use_zfuel_name =
                                               (uu___144_10442.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_10442.current_module_name)
                                           } in
                                         let uu____10443 =
                                           let uu____10444 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10444 in
                                         if uu____10443
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10438 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10454::uu____10455 ->
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
                                                   let uu____10478 =
                                                     let uu____10484 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10484) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10478 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10498 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10500 =
                                             match formals with
                                             | [] ->
                                                 let uu____10509 =
                                                   let uu____10510 =
                                                     let uu____10512 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          Some _0_41)
                                                       uu____10512 in
                                                   push_free_var env1 lid
                                                     vname uu____10510 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10509)
                                             | uu____10515 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10520 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10520 in
                                                 let name_tok_corr =
                                                   let uu____10522 =
                                                     let uu____10526 =
                                                       let uu____10527 =
                                                         let uu____10533 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10533) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10527 in
                                                     (uu____10526,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10522 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10500 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10417 with
                                      | (decls2,env2) ->
                                          let uu____10557 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10562 =
                                              encode_term res_t1 env' in
                                            match uu____10562 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10570 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10570,
                                                  decls) in
                                          (match uu____10557 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10578 =
                                                   let uu____10582 =
                                                     let uu____10583 =
                                                       let uu____10589 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10589) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10583 in
                                                   (uu____10582,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10578 in
                                               let freshness =
                                                 let uu____10598 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10598
                                                 then
                                                   let uu____10601 =
                                                     let uu____10602 =
                                                       let uu____10608 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10614 =
                                                         varops.next_id () in
                                                       (vname, uu____10608,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10614) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10602 in
                                                   let uu____10616 =
                                                     let uu____10618 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10618] in
                                                   uu____10601 :: uu____10616
                                                 else [] in
                                               let g =
                                                 let uu____10622 =
                                                   let uu____10624 =
                                                     let uu____10626 =
                                                       let uu____10628 =
                                                         let uu____10630 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10630 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10628 in
                                                     FStar_List.append decls3
                                                       uu____10626 in
                                                   FStar_List.append decls2
                                                     uu____10624 in
                                                 FStar_List.append decls11
                                                   uu____10622 in
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
          let uu____10656 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10656 with
          | None  ->
              let uu____10679 = encode_free_var env x t t_norm [] in
              (match uu____10679 with
               | (decls,env1) ->
                   let uu____10694 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10694 with
                    | (n1,x',uu____10713) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10725) -> ((n1, x1), [], env)
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
          let uu____10762 = encode_free_var env lid t tt quals in
          match uu____10762 with
          | (decls,env1) ->
              let uu____10773 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10773
              then
                let uu____10777 =
                  let uu____10779 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10779 in
                (uu____10777, env1)
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
             (fun uu____10810  ->
                fun lb  ->
                  match uu____10810 with
                  | (decls,env1) ->
                      let uu____10822 =
                        let uu____10826 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10826
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10822 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10841 = FStar_Syntax_Util.head_and_args t in
    match uu____10841 with
    | (hd1,args) ->
        let uu____10867 =
          let uu____10868 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10868.FStar_Syntax_Syntax.n in
        (match uu____10867 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10872,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10885 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10903  ->
      fun quals  ->
        match uu____10903 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10953 = FStar_Util.first_N nbinders formals in
              match uu____10953 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10995  ->
                         fun uu____10996  ->
                           match (uu____10995, uu____10996) with
                           | ((formal,uu____11006),(binder,uu____11008)) ->
                               let uu____11013 =
                                 let uu____11018 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11018) in
                               FStar_Syntax_Syntax.NT uu____11013) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11023 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11037  ->
                              match uu____11037 with
                              | (x,i) ->
                                  let uu____11044 =
                                    let uu___145_11045 = x in
                                    let uu____11046 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11045.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11045.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11046
                                    } in
                                  (uu____11044, i))) in
                    FStar_All.pipe_right uu____11023
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11058 =
                      let uu____11060 =
                        let uu____11061 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11061.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_42  -> Some _0_42)
                        uu____11060 in
                    let uu____11065 =
                      let uu____11066 = FStar_Syntax_Subst.compress body in
                      let uu____11067 =
                        let uu____11068 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11068 in
                      FStar_Syntax_Syntax.extend_app_n uu____11066
                        uu____11067 in
                    uu____11065 uu____11058 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11110 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11110
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11111 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11111.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11111.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11111.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11111.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11111.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11111.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11111.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11111.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11111.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11111.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11111.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11111.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11111.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11111.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11111.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11111.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11111.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11111.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11111.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11111.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11111.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11111.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11111.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11111.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11111.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11111.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11132 = FStar_Syntax_Util.abs_formals e in
                match uu____11132 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11166::uu____11167 ->
                         let uu____11175 =
                           let uu____11176 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11176.FStar_Syntax_Syntax.n in
                         (match uu____11175 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11203 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11203 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11231 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11231
                                   then
                                     let uu____11254 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11254 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11302  ->
                                                   fun uu____11303  ->
                                                     match (uu____11302,
                                                             uu____11303)
                                                     with
                                                     | ((x,uu____11313),
                                                        (b,uu____11315)) ->
                                                         let uu____11320 =
                                                           let uu____11325 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11325) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11320)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11327 =
                                            let uu____11338 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11338) in
                                          (uu____11327, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11378 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11378 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11430) ->
                              let uu____11435 =
                                let uu____11446 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11446 in
                              (uu____11435, true)
                          | uu____11479 when Prims.op_Negation norm1 ->
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
                          | uu____11481 ->
                              let uu____11482 =
                                let uu____11483 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11484 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11483
                                  uu____11484 in
                              failwith uu____11482)
                     | uu____11497 ->
                         let uu____11498 =
                           let uu____11499 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11499.FStar_Syntax_Syntax.n in
                         (match uu____11498 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11526 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11526 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11544 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11544 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11592 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11620 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11620
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11627 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11668  ->
                            fun lb  ->
                              match uu____11668 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11719 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11719
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11722 =
                                      let uu____11730 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11730
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11722 with
                                    | (tok,decl,env2) ->
                                        let uu____11755 =
                                          let uu____11762 =
                                            let uu____11768 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11768, tok) in
                                          uu____11762 :: toks in
                                        (uu____11755, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11627 with
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
                        | uu____11870 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11875 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11875 vars)
                            else
                              (let uu____11877 =
                                 let uu____11881 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11881) in
                               FStar_SMTEncoding_Util.mkApp uu____11877) in
                      let uu____11886 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11888  ->
                                 match uu___116_11888 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11889 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11892 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11892))) in
                      if uu____11886
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11912;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11914;
                                FStar_Syntax_Syntax.lbeff = uu____11915;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11956 =
                                 let uu____11960 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11960 with
                                 | (tcenv',uu____11971,e_t) ->
                                     let uu____11975 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11982 -> failwith "Impossible" in
                                     (match uu____11975 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_11991 = env1 in
                                            {
                                              bindings =
                                                (uu___149_11991.bindings);
                                              depth = (uu___149_11991.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_11991.warn);
                                              cache = (uu___149_11991.cache);
                                              nolabels =
                                                (uu___149_11991.nolabels);
                                              use_zfuel_name =
                                                (uu___149_11991.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_11991.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_11991.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11956 with
                                | (env',e1,t_norm1) ->
                                    let uu____11998 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11998 with
                                     | ((binders,body,uu____12010,uu____12011),curry)
                                         ->
                                         ((let uu____12018 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12018
                                           then
                                             let uu____12019 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12020 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12019 uu____12020
                                           else ());
                                          (let uu____12022 =
                                             encode_binders None binders env' in
                                           match uu____12022 with
                                           | (vars,guards,env'1,binder_decls,uu____12038)
                                               ->
                                               let body1 =
                                                 let uu____12046 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12046
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12049 =
                                                 let uu____12054 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12054
                                                 then
                                                   let uu____12060 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12061 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12060, uu____12061)
                                                 else
                                                   (let uu____12067 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12067)) in
                                               (match uu____12049 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12081 =
                                                        let uu____12085 =
                                                          let uu____12086 =
                                                            let uu____12092 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12092) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12086 in
                                                        let uu____12098 =
                                                          let uu____12100 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12100 in
                                                        (uu____12085,
                                                          uu____12098,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12081 in
                                                    let uu____12102 =
                                                      let uu____12104 =
                                                        let uu____12106 =
                                                          let uu____12108 =
                                                            let uu____12110 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12110 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12108 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12106 in
                                                      FStar_List.append
                                                        decls1 uu____12104 in
                                                    (uu____12102, env1))))))
                           | uu____12113 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12132 = varops.fresh "fuel" in
                             (uu____12132, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12135 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12174  ->
                                     fun uu____12175  ->
                                       match (uu____12174, uu____12175) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12257 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12257 in
                                           let gtok =
                                             let uu____12259 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12259 in
                                           let env3 =
                                             let uu____12261 =
                                               let uu____12263 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_43  -> Some _0_43)
                                                 uu____12263 in
                                             push_free_var env2 flid gtok
                                               uu____12261 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12135 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12349
                                 t_norm uu____12351 =
                                 match (uu____12349, uu____12351) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12378;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12379;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12396 =
                                       let uu____12400 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12400 with
                                       | (tcenv',uu____12415,e_t) ->
                                           let uu____12419 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12426 ->
                                                 failwith "Impossible" in
                                           (match uu____12419 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_12435 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_12435.bindings);
                                                    depth =
                                                      (uu___150_12435.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_12435.warn);
                                                    cache =
                                                      (uu___150_12435.cache);
                                                    nolabels =
                                                      (uu___150_12435.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_12435.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_12435.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_12435.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12396 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12445 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12445
                                            then
                                              let uu____12446 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12447 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12448 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12446 uu____12447
                                                uu____12448
                                            else ());
                                           (let uu____12450 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12450 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12472 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12472
                                                  then
                                                    let uu____12473 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12474 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12475 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12476 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12473 uu____12474
                                                      uu____12475 uu____12476
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12480 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12480 with
                                                  | (vars,guards,env'1,binder_decls,uu____12498)
                                                      ->
                                                      let decl_g =
                                                        let uu____12506 =
                                                          let uu____12512 =
                                                            let uu____12514 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12514 in
                                                          (g, uu____12512,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12506 in
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
                                                        let uu____12529 =
                                                          let uu____12533 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12533) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12529 in
                                                      let gsapp =
                                                        let uu____12539 =
                                                          let uu____12543 =
                                                            let uu____12545 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12545 ::
                                                              vars_tm in
                                                          (g, uu____12543) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12539 in
                                                      let gmax =
                                                        let uu____12549 =
                                                          let uu____12553 =
                                                            let uu____12555 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12555 ::
                                                              vars_tm in
                                                          (g, uu____12553) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12549 in
                                                      let body1 =
                                                        let uu____12559 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12559
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12561 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12561 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12572
                                                               =
                                                               let uu____12576
                                                                 =
                                                                 let uu____12577
                                                                   =
                                                                   let uu____12585
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
                                                                    uu____12585) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12577 in
                                                               let uu____12596
                                                                 =
                                                                 let uu____12598
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12598 in
                                                               (uu____12576,
                                                                 uu____12596,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12572 in
                                                           let eqn_f =
                                                             let uu____12601
                                                               =
                                                               let uu____12605
                                                                 =
                                                                 let uu____12606
                                                                   =
                                                                   let uu____12612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12612) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12606 in
                                                               (uu____12605,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12601 in
                                                           let eqn_g' =
                                                             let uu____12620
                                                               =
                                                               let uu____12624
                                                                 =
                                                                 let uu____12625
                                                                   =
                                                                   let uu____12631
                                                                    =
                                                                    let uu____12632
                                                                    =
                                                                    let uu____12635
                                                                    =
                                                                    let uu____12636
                                                                    =
                                                                    let uu____12640
                                                                    =
                                                                    let uu____12642
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12642
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12640) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12636 in
                                                                    (gsapp,
                                                                    uu____12635) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12632 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12631) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12625 in
                                                               (uu____12624,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12620 in
                                                           let uu____12654 =
                                                             let uu____12659
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12659
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12676)
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
                                                                    let uu____12691
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12691
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12694
                                                                    =
                                                                    let uu____12698
                                                                    =
                                                                    let uu____12699
                                                                    =
                                                                    let uu____12705
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12705) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12699 in
                                                                    (uu____12698,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12694 in
                                                                 let uu____12716
                                                                   =
                                                                   let uu____12720
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12720
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12728
                                                                    =
                                                                    let uu____12730
                                                                    =
                                                                    let uu____12731
                                                                    =
                                                                    let uu____12735
                                                                    =
                                                                    let uu____12736
                                                                    =
                                                                    let uu____12742
                                                                    =
                                                                    let uu____12743
                                                                    =
                                                                    let uu____12746
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12746,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12743 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12742) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12736 in
                                                                    (uu____12735,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12731 in
                                                                    [uu____12730] in
                                                                    (d3,
                                                                    uu____12728) in
                                                                 (match uu____12716
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12654
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
                               let uu____12781 =
                                 let uu____12788 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12824  ->
                                      fun uu____12825  ->
                                        match (uu____12824, uu____12825) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12911 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12911 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12788 in
                               (match uu____12781 with
                                | (decls2,eqns,env01) ->
                                    let uu____12951 =
                                      let isDeclFun uu___117_12959 =
                                        match uu___117_12959 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12960 -> true
                                        | uu____12966 -> false in
                                      let uu____12967 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12967
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12951 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12994 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12994
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
        let uu____13027 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13027 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13030 = encode_sigelt' env se in
      match uu____13030 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13040 =
                  let uu____13041 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13041 in
                [uu____13040]
            | uu____13042 ->
                let uu____13043 =
                  let uu____13045 =
                    let uu____13046 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13046 in
                  uu____13045 :: g in
                let uu____13047 =
                  let uu____13049 =
                    let uu____13050 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13050 in
                  [uu____13049] in
                FStar_List.append uu____13043 uu____13047 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13060 =
          let uu____13061 = FStar_Syntax_Subst.compress t in
          uu____13061.FStar_Syntax_Syntax.n in
        match uu____13060 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13065)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13068 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13071 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13074 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13076 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13078 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13086 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13089 =
            let uu____13090 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13090 Prims.op_Negation in
          if uu____13089
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13110 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Syntax_Const.effect_Tot_lid None
                                [FStar_Syntax_Syntax.TOTAL])))) None
                     tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13130 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13130 with
               | (aname,atok,env2) ->
                   let uu____13140 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13140 with
                    | (formals,uu____13150) ->
                        let uu____13157 =
                          let uu____13160 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13160 env2 in
                        (match uu____13157 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13168 =
                                 let uu____13169 =
                                   let uu____13175 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13183  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13175,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13169 in
                               [uu____13168;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13190 =
                               let aux uu____13219 uu____13220 =
                                 match (uu____13219, uu____13220) with
                                 | ((bv,uu____13247),(env3,acc_sorts,acc)) ->
                                     let uu____13268 = gen_term_var env3 bv in
                                     (match uu____13268 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13190 with
                              | (uu____13306,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13320 =
                                      let uu____13324 =
                                        let uu____13325 =
                                          let uu____13331 =
                                            let uu____13332 =
                                              let uu____13335 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13335) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13332 in
                                          ([[app]], xs_sorts, uu____13331) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13325 in
                                      (uu____13324, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13320 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13347 =
                                      let uu____13351 =
                                        let uu____13352 =
                                          let uu____13358 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13358) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13352 in
                                      (uu____13351,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13347 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13368 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13368 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13384,uu____13385)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13386 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13386 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13397,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13402 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13404  ->
                      match uu___118_13404 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13405 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13408 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13409 -> false)) in
            Prims.op_Negation uu____13402 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13415 = encode_top_level_val env fv t quals in
             match uu____13415 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13427 =
                   let uu____13429 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13429 in
                 (uu____13427, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13434 = encode_formula f env in
          (match uu____13434 with
           | (f1,decls) ->
               let g =
                 let uu____13443 =
                   let uu____13444 =
                     let uu____13448 =
                       let uu____13450 =
                         let uu____13451 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13451 in
                       Some uu____13450 in
                     let uu____13452 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13448, uu____13452) in
                   FStar_SMTEncoding_Util.mkAssume uu____13444 in
                 [uu____13443] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13456,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____13464 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13471 =
                       let uu____13476 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13476.FStar_Syntax_Syntax.fv_name in
                     uu____13471.FStar_Syntax_Syntax.v in
                   let uu____13480 =
                     let uu____13481 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13481 in
                   if uu____13480
                   then
                     let val_decl =
                       let uu___151_13496 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_13496.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_13496.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13500 = encode_sigelt' env1 val_decl in
                     match uu____13500 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13464 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13517,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13519;
                          FStar_Syntax_Syntax.lbtyp = uu____13520;
                          FStar_Syntax_Syntax.lbeff = uu____13521;
                          FStar_Syntax_Syntax.lbdef = uu____13522;_}::[]),uu____13523,uu____13524)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13538 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13538 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13561 =
                   let uu____13563 =
                     let uu____13564 =
                       let uu____13568 =
                         let uu____13569 =
                           let uu____13575 =
                             let uu____13576 =
                               let uu____13579 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13579) in
                             FStar_SMTEncoding_Util.mkEq uu____13576 in
                           ([[b2t_x]], [xx], uu____13575) in
                         FStar_SMTEncoding_Util.mkForall uu____13569 in
                       (uu____13568, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13564 in
                   [uu____13563] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13561 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13596,uu____13597,uu____13598)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13604  ->
                  match uu___119_13604 with
                  | FStar_Syntax_Syntax.Discriminator uu____13605 -> true
                  | uu____13606 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13608,lids,uu____13610) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13617 =
                     let uu____13618 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13618.FStar_Ident.idText in
                   uu____13617 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13620  ->
                     match uu___120_13620 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13621 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13624,uu____13625)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13635  ->
                  match uu___121_13635 with
                  | FStar_Syntax_Syntax.Projector uu____13636 -> true
                  | uu____13639 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13646 = try_lookup_free_var env l in
          (match uu____13646 with
           | Some uu____13650 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_13653 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_13653.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_13653.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13659,uu____13660) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13672) ->
          let uu____13677 = encode_sigelts env ses in
          (match uu____13677 with
           | (g,env1) ->
               let uu____13687 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13697  ->
                         match uu___122_13697 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13698;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13699;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13700;_}
                             -> false
                         | uu____13702 -> true)) in
               (match uu____13687 with
                | (g',inversions) ->
                    let uu____13711 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13721  ->
                              match uu___123_13721 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13722 ->
                                  true
                              | uu____13728 -> false)) in
                    (match uu____13711 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13739,tps,k,uu____13742,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13752  ->
                    match uu___124_13752 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13753 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13760 = c in
              match uu____13760 with
              | (name,args,uu____13764,uu____13765,uu____13766) ->
                  let uu____13769 =
                    let uu____13770 =
                      let uu____13776 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13783  ->
                                match uu____13783 with
                                | (uu____13787,sort,uu____13789) -> sort)) in
                      (name, uu____13776, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13770 in
                  [uu____13769]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13807 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13810 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13810 FStar_Option.isNone)) in
            if uu____13807
            then []
            else
              (let uu____13827 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13827 with
               | (xxsym,xx) ->
                   let uu____13833 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13844  ->
                             fun l  ->
                               match uu____13844 with
                               | (out,decls) ->
                                   let uu____13856 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13856 with
                                    | (uu____13862,data_t) ->
                                        let uu____13864 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13864 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13893 =
                                                 let uu____13894 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13894.FStar_Syntax_Syntax.n in
                                               match uu____13893 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13902,indices) ->
                                                   indices
                                               | uu____13918 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13930  ->
                                                         match uu____13930
                                                         with
                                                         | (x,uu____13934) ->
                                                             let uu____13935
                                                               =
                                                               let uu____13936
                                                                 =
                                                                 let uu____13940
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13940,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13936 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13935)
                                                    env) in
                                             let uu____13942 =
                                               encode_args indices env1 in
                                             (match uu____13942 with
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
                                                      let uu____13966 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13974
                                                                 =
                                                                 let uu____13977
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13977,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13974)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13966
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13979 =
                                                      let uu____13980 =
                                                        let uu____13983 =
                                                          let uu____13984 =
                                                            let uu____13987 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13987,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13984 in
                                                        (out, uu____13983) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13980 in
                                                    (uu____13979,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13833 with
                    | (data_ax,decls) ->
                        let uu____13995 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13995 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14009 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14009 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14012 =
                                 let uu____14016 =
                                   let uu____14017 =
                                     let uu____14023 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14031 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14023,
                                       uu____14031) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14017 in
                                 let uu____14039 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14016, (Some "inversion axiom"),
                                   uu____14039) in
                               FStar_SMTEncoding_Util.mkAssume uu____14012 in
                             let pattern_guarded_inversion =
                               let uu____14043 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14043
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14054 =
                                   let uu____14055 =
                                     let uu____14059 =
                                       let uu____14060 =
                                         let uu____14066 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14074 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14066, uu____14074) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14060 in
                                     let uu____14082 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14059, (Some "inversion axiom"),
                                       uu____14082) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14055 in
                                 [uu____14054]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14085 =
            let uu____14093 =
              let uu____14094 = FStar_Syntax_Subst.compress k in
              uu____14094.FStar_Syntax_Syntax.n in
            match uu____14093 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14123 -> (tps, k) in
          (match uu____14085 with
           | (formals,res) ->
               let uu____14138 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14138 with
                | (formals1,res1) ->
                    let uu____14145 = encode_binders None formals1 env in
                    (match uu____14145 with
                     | (vars,guards,env',binder_decls,uu____14160) ->
                         let uu____14167 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14167 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14180 =
                                  let uu____14184 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14184) in
                                FStar_SMTEncoding_Util.mkApp uu____14180 in
                              let uu____14189 =
                                let tname_decl =
                                  let uu____14195 =
                                    let uu____14196 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14211  ->
                                              match uu____14211 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14219 = varops.next_id () in
                                    (tname, uu____14196,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14219, false) in
                                  constructor_or_logic_type_decl uu____14195 in
                                let uu____14224 =
                                  match vars with
                                  | [] ->
                                      let uu____14231 =
                                        let uu____14232 =
                                          let uu____14234 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_44  -> Some _0_44)
                                            uu____14234 in
                                        push_free_var env1 t tname
                                          uu____14232 in
                                      ([], uu____14231)
                                  | uu____14238 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14244 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14244 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14253 =
                                          let uu____14257 =
                                            let uu____14258 =
                                              let uu____14266 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14266) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14258 in
                                          (uu____14257,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14253 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14224 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14189 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14289 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14289 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14306 =
                                               let uu____14307 =
                                                 let uu____14311 =
                                                   let uu____14312 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14312 in
                                                 (uu____14311,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14307 in
                                             [uu____14306]
                                           else [] in
                                         let uu____14315 =
                                           let uu____14317 =
                                             let uu____14319 =
                                               let uu____14320 =
                                                 let uu____14324 =
                                                   let uu____14325 =
                                                     let uu____14331 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14331) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14325 in
                                                 (uu____14324, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14320 in
                                             [uu____14319] in
                                           FStar_List.append karr uu____14317 in
                                         FStar_List.append decls1 uu____14315 in
                                   let aux =
                                     let uu____14340 =
                                       let uu____14342 =
                                         inversion_axioms tapp vars in
                                       let uu____14344 =
                                         let uu____14346 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14346] in
                                       FStar_List.append uu____14342
                                         uu____14344 in
                                     FStar_List.append kindingAx uu____14340 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14351,uu____14352,uu____14353,uu____14354,uu____14355)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14360,t,uu____14362,n_tps,uu____14364) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14369 = new_term_constant_and_tok_from_lid env d in
          (match uu____14369 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14380 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14380 with
                | (formals,t_res) ->
                    let uu____14402 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14402 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14411 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14411 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14449 =
                                            mk_term_projector_name d x in
                                          (uu____14449,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14451 =
                                  let uu____14461 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14461, true) in
                                FStar_All.pipe_right uu____14451
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
                              let uu____14483 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14483 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14491::uu____14492 ->
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
                                         let uu____14517 =
                                           let uu____14523 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14523) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14517
                                     | uu____14536 -> tok_typing in
                                   let uu____14541 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14541 with
                                    | (vars',guards',env'',decls_formals,uu____14556)
                                        ->
                                        let uu____14563 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14563 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14582 ->
                                                   let uu____14586 =
                                                     let uu____14587 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14587 in
                                                   [uu____14586] in
                                             let encode_elim uu____14594 =
                                               let uu____14595 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14595 with
                                               | (head1,args) ->
                                                   let uu____14624 =
                                                     let uu____14625 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14625.FStar_Syntax_Syntax.n in
                                                   (match uu____14624 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14632;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14633;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14634;_},uu____14635)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14645 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14645
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
                                                                 | uu____14671
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14679
                                                                    =
                                                                    let uu____14680
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14680 in
                                                                    if
                                                                    uu____14679
                                                                    then
                                                                    let uu____14687
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14687]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14689
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14702
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14702
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14724
                                                                    =
                                                                    let uu____14728
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14728 in
                                                                    (match uu____14724
                                                                    with
                                                                    | 
                                                                    (uu____14735,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14741
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14741
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14743
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14743
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
                                                             (match uu____14689
                                                              with
                                                              | (uu____14751,arg_vars,elim_eqns_or_guards,uu____14754)
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
                                                                    let uu____14773
                                                                    =
                                                                    let uu____14777
                                                                    =
                                                                    let uu____14778
                                                                    =
                                                                    let uu____14784
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14790
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    let uu____14794
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14794) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14791 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14784,
                                                                    uu____14790) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14778 in
                                                                    (uu____14777,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14773 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14807
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14807,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14809
                                                                    =
                                                                    let uu____14813
                                                                    =
                                                                    let uu____14814
                                                                    =
                                                                    let uu____14820
                                                                    =
                                                                    let uu____14823
                                                                    =
                                                                    let uu____14825
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14825] in
                                                                    [uu____14823] in
                                                                    let uu____14828
                                                                    =
                                                                    let uu____14829
                                                                    =
                                                                    let uu____14832
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14833
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14832,
                                                                    uu____14833) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14829 in
                                                                    (uu____14820,
                                                                    [x],
                                                                    uu____14828) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14814 in
                                                                    let uu____14843
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14813,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14843) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14809
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14848
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
                                                                    (let uu____14863
                                                                    =
                                                                    let uu____14864
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14864
                                                                    dapp1 in
                                                                    [uu____14863]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14848
                                                                    FStar_List.flatten in
                                                                    let uu____14868
                                                                    =
                                                                    let uu____14872
                                                                    =
                                                                    let uu____14873
                                                                    =
                                                                    let uu____14879
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14885
                                                                    =
                                                                    let uu____14886
                                                                    =
                                                                    let uu____14889
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14889) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14886 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14879,
                                                                    uu____14885) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14873 in
                                                                    (uu____14872,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14868) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14905 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14905
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
                                                                 | uu____14931
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14939
                                                                    =
                                                                    let uu____14940
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14940 in
                                                                    if
                                                                    uu____14939
                                                                    then
                                                                    let uu____14947
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14947]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14949
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14962
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14962
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14984
                                                                    =
                                                                    let uu____14988
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14988 in
                                                                    (match uu____14984
                                                                    with
                                                                    | 
                                                                    (uu____14995,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15001
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15001
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15003
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15003
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
                                                             (match uu____14949
                                                              with
                                                              | (uu____15011,arg_vars,elim_eqns_or_guards,uu____15014)
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
                                                                    let uu____15033
                                                                    =
                                                                    let uu____15037
                                                                    =
                                                                    let uu____15038
                                                                    =
                                                                    let uu____15044
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15050
                                                                    =
                                                                    let uu____15051
                                                                    =
                                                                    let uu____15054
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15054) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15051 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15044,
                                                                    uu____15050) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15038 in
                                                                    (uu____15037,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15033 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15067
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15067,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15069
                                                                    =
                                                                    let uu____15073
                                                                    =
                                                                    let uu____15074
                                                                    =
                                                                    let uu____15080
                                                                    =
                                                                    let uu____15083
                                                                    =
                                                                    let uu____15085
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15085] in
                                                                    [uu____15083] in
                                                                    let uu____15088
                                                                    =
                                                                    let uu____15089
                                                                    =
                                                                    let uu____15092
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15093
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15092,
                                                                    uu____15093) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15089 in
                                                                    (uu____15080,
                                                                    [x],
                                                                    uu____15088) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15074 in
                                                                    let uu____15103
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15073,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15103) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15069
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15108
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
                                                                    (let uu____15123
                                                                    =
                                                                    let uu____15124
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15124
                                                                    dapp1 in
                                                                    [uu____15123]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15108
                                                                    FStar_List.flatten in
                                                                    let uu____15128
                                                                    =
                                                                    let uu____15132
                                                                    =
                                                                    let uu____15133
                                                                    =
                                                                    let uu____15139
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15145
                                                                    =
                                                                    let uu____15146
                                                                    =
                                                                    let uu____15149
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15149) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15146 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15139,
                                                                    uu____15145) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15133 in
                                                                    (uu____15132,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15128) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15159 ->
                                                        ((let uu____15161 =
                                                            let uu____15162 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15163 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15162
                                                              uu____15163 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15161);
                                                         ([], []))) in
                                             let uu____15166 = encode_elim () in
                                             (match uu____15166 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15178 =
                                                      let uu____15180 =
                                                        let uu____15182 =
                                                          let uu____15184 =
                                                            let uu____15186 =
                                                              let uu____15187
                                                                =
                                                                let uu____15193
                                                                  =
                                                                  let uu____15195
                                                                    =
                                                                    let uu____15196
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15196 in
                                                                  Some
                                                                    uu____15195 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15193) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15187 in
                                                            [uu____15186] in
                                                          let uu____15199 =
                                                            let uu____15201 =
                                                              let uu____15203
                                                                =
                                                                let uu____15205
                                                                  =
                                                                  let uu____15207
                                                                    =
                                                                    let uu____15209
                                                                    =
                                                                    let uu____15211
                                                                    =
                                                                    let uu____15212
                                                                    =
                                                                    let uu____15216
                                                                    =
                                                                    let uu____15217
                                                                    =
                                                                    let uu____15223
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15223) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15217 in
                                                                    (uu____15216,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15212 in
                                                                    let uu____15230
                                                                    =
                                                                    let uu____15232
                                                                    =
                                                                    let uu____15233
                                                                    =
                                                                    let uu____15237
                                                                    =
                                                                    let uu____15238
                                                                    =
                                                                    let uu____15244
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15250
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15244,
                                                                    uu____15250) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15238 in
                                                                    (uu____15237,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15233 in
                                                                    [uu____15232] in
                                                                    uu____15211
                                                                    ::
                                                                    uu____15230 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15209 in
                                                                  FStar_List.append
                                                                    uu____15207
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15205 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15203 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15201 in
                                                          FStar_List.append
                                                            uu____15184
                                                            uu____15199 in
                                                        FStar_List.append
                                                          decls3 uu____15182 in
                                                      FStar_List.append
                                                        decls2 uu____15180 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15178 in
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
           (fun uu____15271  ->
              fun se  ->
                match uu____15271 with
                | (g,env1) ->
                    let uu____15283 = encode_sigelt env1 se in
                    (match uu____15283 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15321 =
        match uu____15321 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15339 ->
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
                 ((let uu____15344 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15344
                   then
                     let uu____15345 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15346 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15347 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15345 uu____15346 uu____15347
                   else ());
                  (let uu____15349 = encode_term t1 env1 in
                   match uu____15349 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15359 =
                         let uu____15363 =
                           let uu____15364 =
                             let uu____15365 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15365
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15364 in
                         new_term_constant_from_string env1 x uu____15363 in
                       (match uu____15359 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15376 = FStar_Options.log_queries () in
                              if uu____15376
                              then
                                let uu____15378 =
                                  let uu____15379 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15380 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15381 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15379 uu____15380 uu____15381 in
                                Some uu____15378
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15392,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15401 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15401 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15414,se,uu____15416) ->
                 let uu____15419 = encode_sigelt env1 se in
                 (match uu____15419 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15429,se) ->
                 let uu____15433 = encode_sigelt env1 se in
                 (match uu____15433 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15443 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15443 with | (uu____15455,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15503  ->
            match uu____15503 with
            | (l,uu____15510,uu____15511) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15532  ->
            match uu____15532 with
            | (l,uu____15540,uu____15541) ->
                let uu____15546 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45) (
                    fst l) in
                let uu____15547 =
                  let uu____15549 =
                    let uu____15550 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15550 in
                  [uu____15549] in
                uu____15546 :: uu____15547)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15562 =
      let uu____15564 =
        let uu____15565 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15567 =
          let uu____15568 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15568 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15565;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15567
        } in
      [uu____15564] in
    FStar_ST.write last_env uu____15562
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15580 = FStar_ST.read last_env in
      match uu____15580 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15586 ->
          let uu___153_15588 = e in
          let uu____15589 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_15588.bindings);
            depth = (uu___153_15588.depth);
            tcenv;
            warn = (uu___153_15588.warn);
            cache = (uu___153_15588.cache);
            nolabels = (uu___153_15588.nolabels);
            use_zfuel_name = (uu___153_15588.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_15588.encode_non_total_function_typ);
            current_module_name = uu____15589
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15594 = FStar_ST.read last_env in
    match uu____15594 with
    | [] -> failwith "Empty env stack"
    | uu____15599::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15608  ->
    let uu____15609 = FStar_ST.read last_env in
    match uu____15609 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_15620 = hd1 in
          {
            bindings = (uu___154_15620.bindings);
            depth = (uu___154_15620.depth);
            tcenv = (uu___154_15620.tcenv);
            warn = (uu___154_15620.warn);
            cache = refs;
            nolabels = (uu___154_15620.nolabels);
            use_zfuel_name = (uu___154_15620.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15620.encode_non_total_function_typ);
            current_module_name = (uu___154_15620.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15627  ->
    let uu____15628 = FStar_ST.read last_env in
    match uu____15628 with
    | [] -> failwith "Popping an empty stack"
    | uu____15633::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15642  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15646  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15650  ->
    let uu____15651 = FStar_ST.read last_env in
    match uu____15651 with
    | hd1::uu____15657::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15663 -> failwith "Impossible"
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
        | (uu____15722::uu____15723,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_15727 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_15727.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_15727.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_15727.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15728 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15741 =
        let uu____15743 =
          let uu____15744 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15744 in
        let uu____15745 = open_fact_db_tags env in uu____15743 :: uu____15745 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15741
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
      let uu____15762 = encode_sigelt env se in
      match uu____15762 with
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
        let uu____15789 = FStar_Options.log_queries () in
        if uu____15789
        then
          let uu____15791 =
            let uu____15792 =
              let uu____15793 =
                let uu____15794 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15794 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15793 in
            FStar_SMTEncoding_Term.Caption uu____15792 in
          uu____15791 :: decls
        else decls in
      let env =
        let uu____15801 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15801 tcenv in
      let uu____15802 = encode_top_level_facts env se in
      match uu____15802 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15811 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15811))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15824 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15824
       then
         let uu____15825 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15825
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15848  ->
                 fun se  ->
                   match uu____15848 with
                   | (g,env2) ->
                       let uu____15860 = encode_top_level_facts env2 se in
                       (match uu____15860 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15873 =
         encode_signature
           (let uu___156_15877 = env in
            {
              bindings = (uu___156_15877.bindings);
              depth = (uu___156_15877.depth);
              tcenv = (uu___156_15877.tcenv);
              warn = false;
              cache = (uu___156_15877.cache);
              nolabels = (uu___156_15877.nolabels);
              use_zfuel_name = (uu___156_15877.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_15877.encode_non_total_function_typ);
              current_module_name = (uu___156_15877.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15873 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15889 = FStar_Options.log_queries () in
             if uu____15889
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_15894 = env1 in
               {
                 bindings = (uu___157_15894.bindings);
                 depth = (uu___157_15894.depth);
                 tcenv = (uu___157_15894.tcenv);
                 warn = true;
                 cache = (uu___157_15894.cache);
                 nolabels = (uu___157_15894.nolabels);
                 use_zfuel_name = (uu___157_15894.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_15894.encode_non_total_function_typ);
                 current_module_name = (uu___157_15894.current_module_name)
               });
            (let uu____15896 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15896
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
        (let uu____15934 =
           let uu____15935 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15935.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15934);
        (let env =
           let uu____15937 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15937 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15944 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15965 = aux rest in
                 (match uu____15965 with
                  | (out,rest1) ->
                      let t =
                        let uu____15983 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15983 with
                        | Some uu____15987 ->
                            let uu____15988 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15988
                              x.FStar_Syntax_Syntax.sort
                        | uu____15989 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15992 =
                        let uu____15994 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_15995 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_15995.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_15995.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15994 :: out in
                      (uu____15992, rest1))
             | uu____15998 -> ([], bindings1) in
           let uu____16002 = aux bindings in
           match uu____16002 with
           | (closing,bindings1) ->
               let uu____16016 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16016, bindings1) in
         match uu____15944 with
         | (q1,bindings1) ->
             let uu____16029 =
               let uu____16032 =
                 FStar_List.filter
                   (fun uu___125_16034  ->
                      match uu___125_16034 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16035 ->
                          false
                      | uu____16039 -> true) bindings1 in
               encode_env_bindings env uu____16032 in
             (match uu____16029 with
              | (env_decls,env1) ->
                  ((let uu____16050 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16050
                    then
                      let uu____16051 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16051
                    else ());
                   (let uu____16053 = encode_formula q1 env1 in
                    match uu____16053 with
                    | (phi,qdecls) ->
                        let uu____16065 =
                          let uu____16068 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16068 phi in
                        (match uu____16065 with
                         | (labels,phi1) ->
                             let uu____16078 = encode_labels labels in
                             (match uu____16078 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16099 =
                                      let uu____16103 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16104 =
                                        varops.mk_unique "@query" in
                                      (uu____16103, (Some "query"),
                                        uu____16104) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16099 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16119 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16119 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16121 = encode_formula q env in
       match uu____16121 with
       | (f,uu____16125) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16127) -> true
             | uu____16130 -> false)))