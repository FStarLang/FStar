open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___101_74  ->
       match uu___101_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      Some uu____114
  | uu____126 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___125_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___125_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___125_140.FStar_Syntax_Syntax.sort)
        } in
      let uu____142 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____142
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____155 =
          let uu____156 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____156 in
        let uu____157 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____157 with
        | (uu____160,t) ->
            let uu____162 =
              let uu____163 = FStar_Syntax_Subst.compress t in
              uu____163.FStar_Syntax_Syntax.n in
            (match uu____162 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____178 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____178 with
                  | (binders,uu____182) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid (fst b)))
             | uu____195 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____202 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____202
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____209 =
        let uu____212 = mk_term_projector_name lid a in
        (uu____212,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____209
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____219 =
        let uu____222 = mk_term_projector_name_by_pos lid i in
        (uu____222,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____219
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
  let new_scope uu____809 =
    let uu____810 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____812 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____810, uu____812) in
  let scopes =
    let uu____823 = let uu____829 = new_scope () in [uu____829] in
    FStar_Util.mk_ref uu____823 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____854 =
        let uu____856 = FStar_ST.read scopes in
        FStar_Util.find_map uu____856
          (fun uu____873  ->
             match uu____873 with
             | (names1,uu____880) -> FStar_Util.smap_try_find names1 y1) in
      match uu____854 with
      | None  -> y1
      | Some uu____885 ->
          (FStar_Util.incr ctr;
           (let uu____890 =
              let uu____891 =
                let uu____892 = FStar_ST.read ctr in
                Prims.string_of_int uu____892 in
              Prims.strcat "__" uu____891 in
            Prims.strcat y1 uu____890)) in
    let top_scope =
      let uu____897 =
        let uu____902 = FStar_ST.read scopes in FStar_List.hd uu____902 in
      FStar_All.pipe_left FStar_Pervasives.fst uu____897 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____941 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____952 =
      let uu____953 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____953 in
    FStar_Util.format2 "%s_%s" pfx uu____952 in
  let string_const s =
    let uu____958 =
      let uu____960 = FStar_ST.read scopes in
      FStar_Util.find_map uu____960
        (fun uu____977  ->
           match uu____977 with
           | (uu____983,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____958 with
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____992 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____992 in
        let top_scope =
          let uu____995 =
            let uu____1000 = FStar_ST.read scopes in FStar_List.hd uu____1000 in
          FStar_All.pipe_left FStar_Pervasives.snd uu____995 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____1028 =
    let uu____1029 =
      let uu____1035 = new_scope () in
      let uu____1040 = FStar_ST.read scopes in uu____1035 :: uu____1040 in
    FStar_ST.write scopes uu____1029 in
  let pop1 uu____1067 =
    let uu____1068 =
      let uu____1074 = FStar_ST.read scopes in FStar_List.tl uu____1074 in
    FStar_ST.write scopes uu____1068 in
  let mark1 uu____1101 = push1 () in
  let reset_mark1 uu____1105 = pop1 () in
  let commit_mark1 uu____1109 =
    let uu____1110 = FStar_ST.read scopes in
    match uu____1110 with
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
    | uu____1170 -> failwith "Impossible" in
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
    let uu___126_1179 = x in
    let uu____1180 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____1180;
      FStar_Syntax_Syntax.index = (uu___126_1179.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___126_1179.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1203 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1227 -> false
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
         (fun uu___102_1529  ->
            match uu___102_1529 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1532 -> [])) in
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
    let uu____1540 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1544  ->
              match uu___103_1544 with
              | Binding_var (x,uu____1546) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1548,uu____1549,uu____1550) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1540 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1583 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1583
      then
        let uu____1585 = FStar_Syntax_Print.term_to_string t in
        Some uu____1585
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1596 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1596)
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
        (let uu___127_1608 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___127_1608.tcenv);
           warn = (uu___127_1608.warn);
           cache = (uu___127_1608.cache);
           nolabels = (uu___127_1608.nolabels);
           use_zfuel_name = (uu___127_1608.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___127_1608.encode_non_total_function_typ);
           current_module_name = (uu___127_1608.current_module_name)
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
        (let uu___128_1621 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___128_1621.depth);
           tcenv = (uu___128_1621.tcenv);
           warn = (uu___128_1621.warn);
           cache = (uu___128_1621.cache);
           nolabels = (uu___128_1621.nolabels);
           use_zfuel_name = (uu___128_1621.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1621.encode_non_total_function_typ);
           current_module_name = (uu___128_1621.current_module_name)
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
          (let uu___129_1637 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___129_1637.depth);
             tcenv = (uu___129_1637.tcenv);
             warn = (uu___129_1637.warn);
             cache = (uu___129_1637.cache);
             nolabels = (uu___129_1637.nolabels);
             use_zfuel_name = (uu___129_1637.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___129_1637.encode_non_total_function_typ);
             current_module_name = (uu___129_1637.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___130_1647 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___130_1647.depth);
          tcenv = (uu___130_1647.tcenv);
          warn = (uu___130_1647.warn);
          cache = (uu___130_1647.cache);
          nolabels = (uu___130_1647.nolabels);
          use_zfuel_name = (uu___130_1647.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___130_1647.encode_non_total_function_typ);
          current_module_name = (uu___130_1647.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1663  ->
             match uu___104_1663 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1671 -> None) in
      let uu____1674 = aux a in
      match uu____1674 with
      | None  ->
          let a2 = unmangle a in
          let uu____1681 = aux a2 in
          (match uu____1681 with
           | None  ->
               let uu____1687 =
                 let uu____1688 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1689 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1688 uu____1689 in
               failwith uu____1687
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1709 =
        let uu___131_1710 = env in
        let uu____1711 =
          let uu____1713 =
            let uu____1714 =
              let uu____1721 =
                let uu____1723 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1723 in
              (x, fname, uu____1721, None) in
            Binding_fvar uu____1714 in
          uu____1713 :: (env.bindings) in
        {
          bindings = uu____1711;
          depth = (uu___131_1710.depth);
          tcenv = (uu___131_1710.tcenv);
          warn = (uu___131_1710.warn);
          cache = (uu___131_1710.cache);
          nolabels = (uu___131_1710.nolabels);
          use_zfuel_name = (uu___131_1710.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1710.encode_non_total_function_typ);
          current_module_name = (uu___131_1710.current_module_name)
        } in
      (fname, ftok, uu____1709)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1745  ->
           match uu___105_1745 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1767 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1779 =
        lookup_binding env
          (fun uu___106_1781  ->
             match uu___106_1781 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1791 -> None) in
      FStar_All.pipe_right uu____1779 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1804 = try_lookup_lid env a in
      match uu____1804 with
      | None  ->
          let uu____1821 =
            let uu____1822 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1822 in
          failwith uu____1821
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
          let uu___132_1853 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___132_1853.depth);
            tcenv = (uu___132_1853.tcenv);
            warn = (uu___132_1853.warn);
            cache = (uu___132_1853.cache);
            nolabels = (uu___132_1853.nolabels);
            use_zfuel_name = (uu___132_1853.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___132_1853.encode_non_total_function_typ);
            current_module_name = (uu___132_1853.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1865 = lookup_lid env x in
        match uu____1865 with
        | (t1,t2,uu____1873) ->
            let t3 =
              let uu____1879 =
                let uu____1883 =
                  let uu____1885 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1885] in
                (f, uu____1883) in
              FStar_SMTEncoding_Util.mkApp uu____1879 in
            let uu___133_1888 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___133_1888.depth);
              tcenv = (uu___133_1888.tcenv);
              warn = (uu___133_1888.warn);
              cache = (uu___133_1888.cache);
              nolabels = (uu___133_1888.nolabels);
              use_zfuel_name = (uu___133_1888.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___133_1888.encode_non_total_function_typ);
              current_module_name = (uu___133_1888.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____1898 = try_lookup_lid env l in
      match uu____1898 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1925 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1930,fuel::[]) ->
                         let uu____1933 =
                           let uu____1934 =
                             let uu____1935 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1935
                               FStar_Pervasives.fst in
                           FStar_Util.starts_with uu____1934 "fuel" in
                         if uu____1933
                         then
                           let uu____1937 =
                             let uu____1938 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1938
                               fuel in
                           FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                             uu____1937
                         else Some t
                     | uu____1941 -> Some t)
                | uu____1942 -> None))
let lookup_free_var env a =
  let uu____1960 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1960 with
  | Some t -> t
  | None  ->
      let uu____1963 =
        let uu____1964 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1964 in
      failwith uu____1963
let lookup_free_var_name env a =
  let uu____1981 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1981 with | (x,uu____1988,uu____1989) -> x
let lookup_free_var_sym env a =
  let uu____2013 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____2013 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____2034;
             FStar_SMTEncoding_Term.rng = uu____2035;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____2043 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____2057 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_2066  ->
           match uu___107_2066 with
           | Binding_fvar (uu____2068,nm',tok,uu____2071) when nm = nm' ->
               tok
           | uu____2076 -> None)
let mkForall_fuel' n1 uu____2093 =
  match uu____2093 with
  | (pats,vars,body) ->
      let fallback uu____2109 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____2112 = FStar_Options.unthrottle_inductives () in
      if uu____2112
      then fallback ()
      else
        (let uu____2114 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____2114 with
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
                       | uu____2133 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____2147 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____2147
                     | uu____2149 ->
                         let uu____2150 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____2150 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____2153 -> body in
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
      | FStar_Syntax_Syntax.Tm_arrow uu____2179 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2187 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2192 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2193 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2202 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2217 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2219 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2219 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2233;
             FStar_Syntax_Syntax.pos = uu____2234;
             FStar_Syntax_Syntax.vars = uu____2235;_},uu____2236)
          ->
          let uu____2251 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2251 FStar_Option.isNone
      | uu____2264 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2271 =
        let uu____2272 = FStar_Syntax_Util.un_uinst t in
        uu____2272.FStar_Syntax_Syntax.n in
      match uu____2271 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2275,uu____2276,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_2305  ->
                  match uu___108_2305 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2306 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____2307,uu____2308,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2335 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____2335 FStar_Option.isSome
      | uu____2348 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2355 = head_normal env t in
      if uu____2355
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
    let uu____2366 =
      let uu____2367 = FStar_Syntax_Syntax.null_binder t in [uu____2367] in
    let uu____2368 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____2366 uu____2368 None
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
                    let uu____2395 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2395
                | s ->
                    let uu____2398 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2398) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_2410  ->
    match uu___109_2410 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2411 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____2439;
                       FStar_SMTEncoding_Term.rng = uu____2440;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2454) ->
              let uu____2459 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2473 -> false) args (FStar_List.rev xs)) in
              if uu____2459 then tok_of_name env f else None
          | (uu____2476,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2479 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2481 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2481)) in
              if uu____2479 then Some t else None
          | uu____2484 -> None in
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
    | uu____2643 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2646  ->
    match uu___110_2646 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2648 =
          let uu____2652 =
            let uu____2654 =
              let uu____2655 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2655 in
            [uu____2654] in
          ("FStar.Char.Char", uu____2652) in
        FStar_SMTEncoding_Util.mkApp uu____2648
    | FStar_Const.Const_int (i,None ) ->
        let uu____2663 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2663
    | FStar_Const.Const_int (i,Some uu____2665) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2674) ->
        let uu____2677 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2677
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2681 =
          let uu____2682 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2682 in
        failwith uu____2681
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2701 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2709 ->
            let uu____2714 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2714
        | uu____2715 ->
            if norm1
            then let uu____2716 = whnf env t1 in aux false uu____2716
            else
              (let uu____2718 =
                 let uu____2719 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2720 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2719 uu____2720 in
               failwith uu____2718) in
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
    | uu____2741 ->
        let uu____2742 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2742)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2770::uu____2771::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2774::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2776 -> false
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
        (let uu____2914 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2914
         then
           let uu____2915 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2915
         else ());
        (let uu____2917 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2953  ->
                   fun b  ->
                     match uu____2953 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2996 =
                           let x = unmangle (fst b) in
                           let uu____3005 = gen_term_var env1 x in
                           match uu____3005 with
                           | (xxsym,xx,env') ->
                               let uu____3019 =
                                 let uu____3022 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____3022 env1 xx in
                               (match uu____3019 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2996 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2917 with
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
          let uu____3110 = encode_term t env in
          match uu____3110 with
          | (t1,decls) ->
              let uu____3117 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____3117, decls)
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
          let uu____3125 = encode_term t env in
          match uu____3125 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____3134 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____3134, decls)
               | Some f ->
                   let uu____3136 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____3136, decls))
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
        let uu____3142 = encode_args args_e env in
        match uu____3142 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3154 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____3161 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____3161 in
            let binary arg_tms1 =
              let uu____3170 =
                let uu____3171 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____3171 in
              let uu____3172 =
                let uu____3173 =
                  let uu____3174 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____3174 in
                FStar_SMTEncoding_Term.unboxInt uu____3173 in
              (uu____3170, uu____3172) in
            let mk_default uu____3179 =
              let uu____3180 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____3180 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____3225 = FStar_Options.smtencoding_l_arith_native () in
              if uu____3225
              then
                let uu____3226 = let uu____3227 = mk_args ts in op uu____3227 in
                FStar_All.pipe_right uu____3226 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____3250 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____3250
              then
                let uu____3251 = binary ts in
                match uu____3251 with
                | (t1,t2) ->
                    let uu____3256 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____3256
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3259 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____3259
                 then
                   let uu____3260 = op (binary ts) in
                   FStar_All.pipe_right uu____3260
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
            let uu____3350 =
              let uu____3356 =
                FStar_List.tryFind
                  (fun uu____3368  ->
                     match uu____3368 with
                     | (l,uu____3375) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____3356 FStar_Util.must in
            (match uu____3350 with
             | (uu____3400,op) ->
                 let uu____3408 = op arg_tms in (uu____3408, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____3415 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____3415
       then
         let uu____3416 = FStar_Syntax_Print.tag_of_term t in
         let uu____3417 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____3418 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3416 uu____3417
           uu____3418
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3422 ->
           let uu____3443 =
             let uu____3444 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3445 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3446 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3447 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3444
               uu____3445 uu____3446 uu____3447 in
           failwith uu____3443
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3450 =
             let uu____3451 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____3452 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____3453 = FStar_Syntax_Print.term_to_string t0 in
             let uu____3454 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3451
               uu____3452 uu____3453 uu____3454 in
           failwith uu____3450
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3458 =
             let uu____3459 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3459 in
           failwith uu____3458
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3464) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3494) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3503 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____3503, [])
       | FStar_Syntax_Syntax.Tm_type uu____3509 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3512) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3518 = encode_const c in (uu____3518, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____3533 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____3533 with
            | (binders1,res) ->
                let uu____3540 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____3540
                then
                  let uu____3543 = encode_binders None binders1 env in
                  (match uu____3543 with
                   | (vars,guards,env',decls,uu____3558) ->
                       let fsym =
                         let uu____3568 = varops.fresh "f" in
                         (uu____3568, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____3571 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___134_3575 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___134_3575.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___134_3575.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___134_3575.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___134_3575.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___134_3575.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___134_3575.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___134_3575.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___134_3575.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___134_3575.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___134_3575.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___134_3575.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___134_3575.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___134_3575.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___134_3575.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___134_3575.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___134_3575.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___134_3575.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___134_3575.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___134_3575.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___134_3575.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___134_3575.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___134_3575.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___134_3575.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___134_3575.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___134_3575.FStar_TypeChecker_Env.synth)
                            }) res in
                       (match uu____3571 with
                        | (pre_opt,res_t) ->
                            let uu____3582 =
                              encode_term_pred None res_t env' app in
                            (match uu____3582 with
                             | (res_pred,decls') ->
                                 let uu____3589 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3596 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____3596, [])
                                   | Some pre ->
                                       let uu____3599 =
                                         encode_formula pre env' in
                                       (match uu____3599 with
                                        | (guard,decls0) ->
                                            let uu____3607 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3607, decls0)) in
                                 (match uu____3589 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3615 =
                                          let uu____3621 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3621) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3615 in
                                      let cvars =
                                        let uu____3631 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3631
                                          (FStar_List.filter
                                             (fun uu____3637  ->
                                                match uu____3637 with
                                                | (x,uu____3641) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3652 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3652 with
                                       | Some cache_entry ->
                                           let uu____3657 =
                                             let uu____3658 =
                                               let uu____3662 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3662) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3658 in
                                           (uu____3657,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3673 =
                                               let uu____3674 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3674 in
                                             varops.mk_unique uu____3673 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3681 =
                                               FStar_Options.log_queries () in
                                             if uu____3681
                                             then
                                               let uu____3683 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3683
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3689 =
                                               let uu____3693 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3693) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3689 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3701 =
                                               let uu____3705 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3705, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3701 in
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
                                             let uu____3718 =
                                               let uu____3722 =
                                                 let uu____3723 =
                                                   let uu____3729 =
                                                     let uu____3730 =
                                                       let uu____3733 =
                                                         let uu____3734 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3734 in
                                                       (f_has_t, uu____3733) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3730 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3729) in
                                                 mkForall_fuel uu____3723 in
                                               (uu____3722,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3718 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3747 =
                                               let uu____3751 =
                                                 let uu____3752 =
                                                   let uu____3758 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3758) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3752 in
                                               (uu____3751, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3747 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3772 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3772);
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
                     let uu____3783 =
                       let uu____3787 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3787, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3783 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3796 =
                       let uu____3800 =
                         let uu____3801 =
                           let uu____3807 =
                             let uu____3808 =
                               let uu____3811 =
                                 let uu____3812 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3812 in
                               (f_has_t, uu____3811) in
                             FStar_SMTEncoding_Util.mkImp uu____3808 in
                           ([[f_has_t]], [fsym], uu____3807) in
                         mkForall_fuel uu____3801 in
                       (uu____3800, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3796 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3826 ->
           let uu____3831 =
             let uu____3834 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3834 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3839;
                 FStar_Syntax_Syntax.pos = uu____3840;
                 FStar_Syntax_Syntax.vars = uu____3841;_} ->
                 let uu____3848 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3848 with
                  | (b,f1) ->
                      let uu____3862 =
                        let uu____3863 = FStar_List.hd b in fst uu____3863 in
                      (uu____3862, f1))
             | uu____3868 -> failwith "impossible" in
           (match uu____3831 with
            | (x,f) ->
                let uu____3875 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3875 with
                 | (base_t,decls) ->
                     let uu____3882 = gen_term_var env x in
                     (match uu____3882 with
                      | (x1,xtm,env') ->
                          let uu____3891 = encode_formula f env' in
                          (match uu____3891 with
                           | (refinement,decls') ->
                               let uu____3898 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3898 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3909 =
                                        let uu____3911 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3915 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3911
                                          uu____3915 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3909 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3931  ->
                                              match uu____3931 with
                                              | (y,uu____3935) ->
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
                                    let uu____3954 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3954 with
                                     | Some cache_entry ->
                                         let uu____3959 =
                                           let uu____3960 =
                                             let uu____3964 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3964) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3960 in
                                         (uu____3959,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3976 =
                                             let uu____3977 =
                                               let uu____3978 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3978 in
                                             Prims.strcat module_name
                                               uu____3977 in
                                           varops.mk_unique uu____3976 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3987 =
                                             let uu____3991 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3991) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3987 in
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
                                           let uu____4002 =
                                             let uu____4006 =
                                               let uu____4007 =
                                                 let uu____4013 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4013) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4007 in
                                             (uu____4006,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4002 in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort) in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1]) in
                                           let uu____4028 =
                                             let uu____4032 =
                                               let uu____4033 =
                                                 let uu____4039 =
                                                   let uu____4040 =
                                                     let uu____4043 =
                                                       let uu____4044 =
                                                         let uu____4050 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement) in
                                                         ([], [xx],
                                                           uu____4050) in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4044 in
                                                     (uu____4043, valid_t) in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4040 in
                                                 ([[valid_t]], cvars1,
                                                   uu____4039) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4033 in
                                             (uu____4032,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4028 in
                                         let t_kinding =
                                           let uu____4070 =
                                             let uu____4074 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____4074,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4070 in
                                         let t_interp =
                                           let uu____4084 =
                                             let uu____4088 =
                                               let uu____4089 =
                                                 let uu____4095 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4095) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4089 in
                                             let uu____4107 =
                                               let uu____4109 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____4109 in
                                             (uu____4088, uu____4107,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4084 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____4114 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4114);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4131 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4131 in
           let uu____4132 = encode_term_pred None k env ttm in
           (match uu____4132 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4140 =
                    let uu____4144 =
                      let uu____4145 =
                        let uu____4146 =
                          let uu____4147 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4147 in
                        FStar_Util.format1 "uvar_typing_%s" uu____4146 in
                      varops.mk_unique uu____4145 in
                    (t_has_k, (Some "Uvar typing"), uu____4144) in
                  FStar_SMTEncoding_Util.mkAssume uu____4140 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4150 ->
           let uu____4160 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____4160 with
            | (head1,args_e) ->
                let uu____4188 =
                  let uu____4196 =
                    let uu____4197 = FStar_Syntax_Subst.compress head1 in
                    uu____4197.FStar_Syntax_Syntax.n in
                  (uu____4196, args_e) in
                (match uu____4188 with
                 | uu____4207 when head_redex env head1 ->
                     let uu____4215 = whnf env t in
                     encode_term uu____4215 env
                 | uu____4216 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____4229;
                       FStar_Syntax_Syntax.pos = uu____4230;
                       FStar_Syntax_Syntax.vars = uu____4231;_},uu____4232),uu____4233::
                    (v1,uu____4235)::(v2,uu____4237)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4275 = encode_term v1 env in
                     (match uu____4275 with
                      | (v11,decls1) ->
                          let uu____4282 = encode_term v2 env in
                          (match uu____4282 with
                           | (v21,decls2) ->
                               let uu____4289 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4289,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4292::(v1,uu____4294)::(v2,uu____4296)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4330 = encode_term v1 env in
                     (match uu____4330 with
                      | (v11,decls1) ->
                          let uu____4337 = encode_term v2 env in
                          (match uu____4337 with
                           | (v21,decls2) ->
                               let uu____4344 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____4344,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4346) ->
                     let e0 =
                       let uu____4358 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____4358 in
                     ((let uu____4364 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____4364
                       then
                         let uu____4365 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4365
                       else ());
                      (let e =
                         let uu____4370 =
                           let uu____4371 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____4372 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4371
                             uu____4372 in
                         uu____4370 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4381),(arg,uu____4383)::[]) -> encode_term arg env
                 | uu____4401 ->
                     let uu____4409 = encode_args args_e env in
                     (match uu____4409 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4442 = encode_term head1 env in
                            match uu____4442 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____4481 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____4481 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4525  ->
                                                 fun uu____4526  ->
                                                   match (uu____4525,
                                                           uu____4526)
                                                   with
                                                   | ((bv,uu____4540),
                                                      (a,uu____4542)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____4556 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____4556
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____4561 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____4561 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____4571 =
                                                   let uu____4575 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____4580 =
                                                     let uu____4581 =
                                                       let uu____4582 =
                                                         let uu____4583 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____4583 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4582 in
                                                     varops.mk_unique
                                                       uu____4581 in
                                                   (uu____4575,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4580) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4571 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____4600 = lookup_free_var_sym env fv in
                            match uu____4600 with
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
                                   FStar_Syntax_Syntax.tk = uu____4623;
                                   FStar_Syntax_Syntax.pos = uu____4624;
                                   FStar_Syntax_Syntax.vars = uu____4625;_},uu____4626)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4637;
                                   FStar_Syntax_Syntax.pos = uu____4638;
                                   FStar_Syntax_Syntax.vars = uu____4639;_},uu____4640)
                                ->
                                let uu____4645 =
                                  let uu____4646 =
                                    let uu____4649 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4649
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4646
                                    FStar_Pervasives.snd in
                                Some uu____4645
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4669 =
                                  let uu____4670 =
                                    let uu____4673 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4673
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4670
                                    FStar_Pervasives.snd in
                                Some uu____4669
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4692,(FStar_Util.Inl t1,uu____4694),uu____4695)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4733,(FStar_Util.Inr c,uu____4735),uu____4736)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4774 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4794 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4794 in
                               let uu____4795 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4795 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4805;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4806;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4807;_},uu____4808)
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
                                     | uu____4840 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4890 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4890 with
            | (bs1,body1,opening) ->
                let fallback uu____4905 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4910 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4910, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4921 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4921
                  | FStar_Util.Inr (eff,uu____4923) ->
                      let uu____4929 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4929 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4974 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___135_4975 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___135_4975.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___135_4975.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___135_4975.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___135_4975.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___135_4975.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___135_4975.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___135_4975.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___135_4975.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___135_4975.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___135_4975.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___135_4975.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___135_4975.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___135_4975.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___135_4975.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___135_4975.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___135_4975.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___135_4975.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___135_4975.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___135_4975.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___135_4975.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___135_4975.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___135_4975.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___135_4975.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___135_4975.FStar_TypeChecker_Env.proof_ns);
                               FStar_TypeChecker_Env.synth =
                                 (uu___135_4975.FStar_TypeChecker_Env.synth)
                             }) uu____4974 FStar_Syntax_Syntax.U_unknown in
                        let uu____4976 =
                          let uu____4977 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4977 in
                        FStar_Util.Inl uu____4976
                    | FStar_Util.Inr (eff_name,uu____4984) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____5015 =
                        let uu____5016 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____5016 in
                      FStar_All.pipe_right uu____5015
                        (fun _0_41  -> Some _0_41)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____5028 =
                        let uu____5029 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____5029 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____5037 =
                          let uu____5038 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____5038 in
                        FStar_All.pipe_right uu____5037
                          (fun _0_42  -> Some _0_42)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____5042 =
                             let uu____5043 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____5043 in
                           FStar_All.pipe_right uu____5042
                             (fun _0_43  -> Some _0_43))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____5054 =
                         let uu____5055 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5055 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5054);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____5070 =
                       (is_impure lc1) &&
                         (let uu____5071 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____5071) in
                     if uu____5070
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____5076 = encode_binders None bs1 env in
                        match uu____5076 with
                        | (vars,guards,envbody,decls,uu____5091) ->
                            let uu____5098 =
                              let uu____5106 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____5106
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____5098 with
                             | (lc2,body2) ->
                                 let uu____5131 = encode_term body2 envbody in
                                 (match uu____5131 with
                                  | (body3,decls') ->
                                      let uu____5138 =
                                        let uu____5143 = codomain_eff lc2 in
                                        match uu____5143 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____5155 =
                                              encode_term tfun env in
                                            (match uu____5155 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____5138 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____5174 =
                                               let uu____5180 =
                                                 let uu____5181 =
                                                   let uu____5184 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____5184, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____5181 in
                                               ([], vars, uu____5180) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____5174 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____5192 =
                                                   let uu____5194 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____5194 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____5192 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____5205 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____5205 with
                                            | Some cache_entry ->
                                                let uu____5210 =
                                                  let uu____5211 =
                                                    let uu____5215 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____5215) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5211 in
                                                (uu____5210,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____5221 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____5221 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____5228 =
                                                         let uu____5229 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____5229 =
                                                           cache_size in
                                                       if uu____5228
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
                                                         let uu____5240 =
                                                           let uu____5241 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____5241 in
                                                         varops.mk_unique
                                                           uu____5240 in
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
                                                       let uu____5246 =
                                                         let uu____5250 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____5250) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____5246 in
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
                                                           let uu____5262 =
                                                             let uu____5263 =
                                                               let uu____5267
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____5267,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____5263 in
                                                           [uu____5262] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____5275 =
                                                         let uu____5279 =
                                                           let uu____5280 =
                                                             let uu____5286 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____5286) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____5280 in
                                                         (uu____5279,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____5275 in
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
                                                     ((let uu____5296 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____5296);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5298,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5299;
                          FStar_Syntax_Syntax.lbunivs = uu____5300;
                          FStar_Syntax_Syntax.lbtyp = uu____5301;
                          FStar_Syntax_Syntax.lbeff = uu____5302;
                          FStar_Syntax_Syntax.lbdef = uu____5303;_}::uu____5304),uu____5305)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5323;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5325;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5341 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____5354 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____5354, [decl_e])))
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
              let uu____5396 = encode_term e1 env in
              match uu____5396 with
              | (ee1,decls1) ->
                  let uu____5403 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____5403 with
                   | (xs,e21) ->
                       let uu____5417 = FStar_List.hd xs in
                       (match uu____5417 with
                        | (x1,uu____5425) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____5427 = encode_body e21 env' in
                            (match uu____5427 with
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
            let uu____5449 =
              let uu____5453 =
                let uu____5454 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____5454 in
              gen_term_var env uu____5453 in
            match uu____5449 with
            | (scrsym,scr',env1) ->
                let uu____5464 = encode_term e env1 in
                (match uu____5464 with
                 | (scr,decls) ->
                     let uu____5471 =
                       let encode_branch b uu____5487 =
                         match uu____5487 with
                         | (else_case,decls1) ->
                             let uu____5498 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____5498 with
                              | (p,w,br) ->
                                  let uu____5519 = encode_pat env1 p in
                                  (match uu____5519 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____5539  ->
                                                   match uu____5539 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____5544 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____5559 =
                                               encode_term w1 env2 in
                                             (match uu____5559 with
                                              | (w2,decls2) ->
                                                  let uu____5567 =
                                                    let uu____5568 =
                                                      let uu____5571 =
                                                        let uu____5572 =
                                                          let uu____5575 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____5575) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5572 in
                                                      (guard, uu____5571) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5568 in
                                                  (uu____5567, decls2)) in
                                       (match uu____5544 with
                                        | (guard1,decls2) ->
                                            let uu____5583 =
                                              encode_br br env2 in
                                            (match uu____5583 with
                                             | (br1,decls3) ->
                                                 let uu____5591 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____5591,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____5471 with
                      | (match_tm,decls1) ->
                          let uu____5602 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____5602, decls1)))
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5624 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____5624
       then
         let uu____5625 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5625
       else ());
      (let uu____5627 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____5627 with
       | (vars,pat_term) ->
           let uu____5637 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5660  ->
                     fun v1  ->
                       match uu____5660 with
                       | (env1,vars1) ->
                           let uu____5688 = gen_term_var env1 v1 in
                           (match uu____5688 with
                            | (xx,uu____5700,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____5637 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5747 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5748 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5749 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5755 =
                        let uu____5758 = encode_const c in
                        (scrutinee, uu____5758) in
                      FStar_SMTEncoding_Util.mkEq uu____5755
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5777 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5777 with
                        | (uu____5781,uu____5782::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5784 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5805  ->
                                  match uu____5805 with
                                  | (arg,uu____5811) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5821 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5821)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5841) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5860 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5875 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5897  ->
                                  match uu____5897 with
                                  | (arg,uu____5906) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5916 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5916)) in
                      FStar_All.pipe_right uu____5875 FStar_List.flatten in
                let pat_term1 uu____5932 = encode_term pat_term env1 in
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
      let uu____5939 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5954  ->
                fun uu____5955  ->
                  match (uu____5954, uu____5955) with
                  | ((tms,decls),(t,uu____5975)) ->
                      let uu____5986 = encode_term t env in
                      (match uu____5986 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5939 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____6020 = FStar_Syntax_Util.list_elements e in
        match uu____6020 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____6035 =
          let uu____6045 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____6045 FStar_Syntax_Util.head_and_args in
        match uu____6035 with
        | (head1,args) ->
            let uu____6073 =
              let uu____6081 =
                let uu____6082 = FStar_Syntax_Util.un_uinst head1 in
                uu____6082.FStar_Syntax_Syntax.n in
              (uu____6081, args) in
            (match uu____6073 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6093,uu____6094)::(e,uu____6096)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____6122 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or1 t1 =
          let uu____6149 =
            let uu____6159 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____6159 FStar_Syntax_Util.head_and_args in
          match uu____6149 with
          | (head1,args) ->
              let uu____6188 =
                let uu____6196 =
                  let uu____6197 = FStar_Syntax_Util.un_uinst head1 in
                  uu____6197.FStar_Syntax_Syntax.n in
                (uu____6196, args) in
              (match uu____6188 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6210)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____6230 -> None) in
        match elts with
        | t1::[] ->
            let uu____6245 = smt_pat_or1 t1 in
            (match uu____6245 with
             | Some e ->
                 let uu____6258 = list_elements1 e in
                 FStar_All.pipe_right uu____6258
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6269 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____6269
                           (FStar_List.map one_pat)))
             | uu____6277 ->
                 let uu____6281 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____6281])
        | uu____6297 ->
            let uu____6299 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____6299] in
      let uu____6315 =
        let uu____6328 =
          let uu____6329 = FStar_Syntax_Subst.compress t in
          uu____6329.FStar_Syntax_Syntax.n in
        match uu____6328 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6356 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____6356 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6385;
                        FStar_Syntax_Syntax.effect_name = uu____6386;
                        FStar_Syntax_Syntax.result_typ = uu____6387;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6389)::(post,uu____6391)::(pats,uu____6393)::[];
                        FStar_Syntax_Syntax.flags = uu____6394;_}
                      ->
                      let uu____6426 = lemma_pats pats in
                      (binders1, pre, post, uu____6426)
                  | uu____6439 -> failwith "impos"))
        | uu____6452 -> failwith "Impos" in
      match uu____6315 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6488 = env in
            {
              bindings = (uu___136_6488.bindings);
              depth = (uu___136_6488.depth);
              tcenv = (uu___136_6488.tcenv);
              warn = (uu___136_6488.warn);
              cache = (uu___136_6488.cache);
              nolabels = (uu___136_6488.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6488.encode_non_total_function_typ);
              current_module_name = (uu___136_6488.current_module_name)
            } in
          let uu____6489 = encode_binders None binders env1 in
          (match uu____6489 with
           | (vars,guards,env2,decls,uu____6504) ->
               let uu____6511 =
                 let uu____6518 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6540 =
                             let uu____6545 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6545 FStar_List.unzip in
                           match uu____6540 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____6518 FStar_List.unzip in
               (match uu____6511 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___137_6603 = env2 in
                      {
                        bindings = (uu___137_6603.bindings);
                        depth = (uu___137_6603.depth);
                        tcenv = (uu___137_6603.tcenv);
                        warn = (uu___137_6603.warn);
                        cache = (uu___137_6603.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6603.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6603.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6603.current_module_name)
                      } in
                    let uu____6604 =
                      let uu____6607 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6607 env3 in
                    (match uu____6604 with
                     | (pre1,decls'') ->
                         let uu____6612 =
                           let uu____6615 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6615 env3 in
                         (match uu____6612 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6622 =
                                let uu____6623 =
                                  let uu____6629 =
                                    let uu____6630 =
                                      let uu____6633 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6633, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6630 in
                                  (pats, vars, uu____6629) in
                                FStar_SMTEncoding_Util.mkForall uu____6623 in
                              (uu____6622, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6646 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6646
        then
          let uu____6647 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6648 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6647 uu____6648
        else () in
      let enc f r l =
        let uu____6675 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6688 = encode_term (fst x) env in
                 match uu____6688 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6675 with
        | (decls,args) ->
            let uu____6705 =
              let uu___138_6706 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6706.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6706.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6705, decls) in
      let const_op f r uu____6731 = let uu____6740 = f r in (uu____6740, []) in
      let un_op f l =
        let uu____6756 = FStar_List.hd l in FStar_All.pipe_left f uu____6756 in
      let bin_op f uu___111_6769 =
        match uu___111_6769 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6777 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6804 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6813  ->
                 match uu____6813 with
                 | (t,uu____6821) ->
                     let uu____6822 = encode_formula t env in
                     (match uu____6822 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6804 with
        | (decls,phis) ->
            let uu____6839 =
              let uu___139_6840 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6840.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6840.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6839, decls) in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6879  ->
               match uu____6879 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6893) -> false
                    | uu____6894 -> true)) args in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6907 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf)) in
          failwith uu____6907
        else
          (let uu____6922 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
           uu____6922 r rf) in
      let mk_imp1 r uu___112_6941 =
        match uu___112_6941 with
        | (lhs,uu____6945)::(rhs,uu____6947)::[] ->
            let uu____6968 = encode_formula rhs env in
            (match uu____6968 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6977) ->
                      (l1, decls1)
                  | uu____6980 ->
                      let uu____6981 = encode_formula lhs env in
                      (match uu____6981 with
                       | (l2,decls2) ->
                           let uu____6988 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6988, (FStar_List.append decls1 decls2)))))
        | uu____6990 -> failwith "impossible" in
      let mk_ite r uu___113_7005 =
        match uu___113_7005 with
        | (guard,uu____7009)::(_then,uu____7011)::(_else,uu____7013)::[] ->
            let uu____7042 = encode_formula guard env in
            (match uu____7042 with
             | (g,decls1) ->
                 let uu____7049 = encode_formula _then env in
                 (match uu____7049 with
                  | (t,decls2) ->
                      let uu____7056 = encode_formula _else env in
                      (match uu____7056 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7065 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____7084 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____7084 in
      let connectives =
        let uu____7096 =
          let uu____7105 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____7105) in
        let uu____7118 =
          let uu____7128 =
            let uu____7137 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____7137) in
          let uu____7150 =
            let uu____7160 =
              let uu____7170 =
                let uu____7179 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____7179) in
              let uu____7192 =
                let uu____7202 =
                  let uu____7212 =
                    let uu____7221 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____7221) in
                  [uu____7212;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____7202 in
              uu____7170 :: uu____7192 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____7160 in
          uu____7128 :: uu____7150 in
        uu____7096 :: uu____7118 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7437 = encode_formula phi' env in
            (match uu____7437 with
             | (phi2,decls) ->
                 let uu____7444 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____7444, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7445 ->
            let uu____7450 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____7450 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7479 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____7479 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7487;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7489;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7505 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____7505 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7537::(x,uu____7539)::(t,uu____7541)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7575 = encode_term x env in
                 (match uu____7575 with
                  | (x1,decls) ->
                      let uu____7582 = encode_term t env in
                      (match uu____7582 with
                       | (t1,decls') ->
                           let uu____7589 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7589, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7593)::(msg,uu____7595)::(phi2,uu____7597)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7631 =
                   let uu____7634 =
                     let uu____7635 = FStar_Syntax_Subst.compress r in
                     uu____7635.FStar_Syntax_Syntax.n in
                   let uu____7638 =
                     let uu____7639 = FStar_Syntax_Subst.compress msg in
                     uu____7639.FStar_Syntax_Syntax.n in
                   (uu____7634, uu____7638) in
                 (match uu____7631 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7646))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7662 -> fallback phi2)
             | uu____7665 when head_redex env head2 ->
                 let uu____7673 = whnf env phi1 in
                 encode_formula uu____7673 env
             | uu____7674 ->
                 let uu____7682 = encode_term phi1 env in
                 (match uu____7682 with
                  | (tt,decls) ->
                      let uu____7689 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7690 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7690.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7690.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7689, decls)))
        | uu____7693 ->
            let uu____7694 = encode_term phi1 env in
            (match uu____7694 with
             | (tt,decls) ->
                 let uu____7701 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7702 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7702.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7702.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7701, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7729 = encode_binders None bs env1 in
        match uu____7729 with
        | (vars,guards,env2,decls,uu____7751) ->
            let uu____7758 =
              let uu____7765 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7788 =
                          let uu____7793 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7807  ->
                                    match uu____7807 with
                                    | (t,uu____7813) ->
                                        encode_term t
                                          (let uu___142_7814 = env2 in
                                           {
                                             bindings =
                                               (uu___142_7814.bindings);
                                             depth = (uu___142_7814.depth);
                                             tcenv = (uu___142_7814.tcenv);
                                             warn = (uu___142_7814.warn);
                                             cache = (uu___142_7814.cache);
                                             nolabels =
                                               (uu___142_7814.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7814.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7814.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7793 FStar_List.unzip in
                        match uu____7788 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7765 FStar_List.unzip in
            (match uu____7758 with
             | (pats,decls') ->
                 let uu____7866 = encode_formula body env2 in
                 (match uu____7866 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7885;
                             FStar_SMTEncoding_Term.rng = uu____7886;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7894 -> guards in
                      let uu____7897 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7897, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7931  ->
                   match uu____7931 with
                   | (x,uu____7935) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7941 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7947 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7947) uu____7941 tl1 in
             let uu____7949 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7961  ->
                       match uu____7961 with
                       | (b,uu____7965) ->
                           let uu____7966 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7966)) in
             (match uu____7949 with
              | None  -> ()
              | Some (x,uu____7970) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7980 =
                    let uu____7981 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7981 in
                  FStar_Errors.warn pos uu____7980) in
       let uu____7982 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7982 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7988 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____8024  ->
                     match uu____8024 with
                     | (l,uu____8034) -> FStar_Ident.lid_equals op l)) in
           (match uu____7988 with
            | None  -> fallback phi1
            | Some (uu____8057,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8086 = encode_q_body env vars pats body in
             match uu____8086 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8112 =
                     let uu____8118 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____8118) in
                   FStar_SMTEncoding_Term.mkForall uu____8112
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8130 = encode_q_body env vars pats body in
             match uu____8130 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8155 =
                   let uu____8156 =
                     let uu____8162 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____8162) in
                   FStar_SMTEncoding_Term.mkExists uu____8156
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____8155, decls))))
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
  let uu____8236 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____8236 with
  | (asym,a) ->
      let uu____8241 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____8241 with
       | (xsym,x) ->
           let uu____8246 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____8246 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8276 =
                      let uu____8282 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____8282, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____8276 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____8297 =
                      let uu____8301 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____8301) in
                    FStar_SMTEncoding_Util.mkApp uu____8297 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____8309 =
                    let uu____8311 =
                      let uu____8313 =
                        let uu____8315 =
                          let uu____8316 =
                            let uu____8320 =
                              let uu____8321 =
                                let uu____8327 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____8327) in
                              FStar_SMTEncoding_Util.mkForall uu____8321 in
                            (uu____8320, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____8316 in
                        let uu____8336 =
                          let uu____8338 =
                            let uu____8339 =
                              let uu____8343 =
                                let uu____8344 =
                                  let uu____8350 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____8350) in
                                FStar_SMTEncoding_Util.mkForall uu____8344 in
                              (uu____8343,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____8339 in
                          [uu____8338] in
                        uu____8315 :: uu____8336 in
                      xtok_decl :: uu____8313 in
                    xname_decl :: uu____8311 in
                  (xtok1, uu____8309) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____8399 =
                    let uu____8407 =
                      let uu____8413 =
                        let uu____8414 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8414 in
                      quant axy uu____8413 in
                    (FStar_Syntax_Const.op_Eq, uu____8407) in
                  let uu____8420 =
                    let uu____8429 =
                      let uu____8437 =
                        let uu____8443 =
                          let uu____8444 =
                            let uu____8445 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____8445 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8444 in
                        quant axy uu____8443 in
                      (FStar_Syntax_Const.op_notEq, uu____8437) in
                    let uu____8451 =
                      let uu____8460 =
                        let uu____8468 =
                          let uu____8474 =
                            let uu____8475 =
                              let uu____8476 =
                                let uu____8479 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8480 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____8479, uu____8480) in
                              FStar_SMTEncoding_Util.mkLT uu____8476 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8475 in
                          quant xy uu____8474 in
                        (FStar_Syntax_Const.op_LT, uu____8468) in
                      let uu____8486 =
                        let uu____8495 =
                          let uu____8503 =
                            let uu____8509 =
                              let uu____8510 =
                                let uu____8511 =
                                  let uu____8514 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____8515 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____8514, uu____8515) in
                                FStar_SMTEncoding_Util.mkLTE uu____8511 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8510 in
                            quant xy uu____8509 in
                          (FStar_Syntax_Const.op_LTE, uu____8503) in
                        let uu____8521 =
                          let uu____8530 =
                            let uu____8538 =
                              let uu____8544 =
                                let uu____8545 =
                                  let uu____8546 =
                                    let uu____8549 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____8550 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____8549, uu____8550) in
                                  FStar_SMTEncoding_Util.mkGT uu____8546 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8545 in
                              quant xy uu____8544 in
                            (FStar_Syntax_Const.op_GT, uu____8538) in
                          let uu____8556 =
                            let uu____8565 =
                              let uu____8573 =
                                let uu____8579 =
                                  let uu____8580 =
                                    let uu____8581 =
                                      let uu____8584 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8585 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8584, uu____8585) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8581 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8580 in
                                quant xy uu____8579 in
                              (FStar_Syntax_Const.op_GTE, uu____8573) in
                            let uu____8591 =
                              let uu____8600 =
                                let uu____8608 =
                                  let uu____8614 =
                                    let uu____8615 =
                                      let uu____8616 =
                                        let uu____8619 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8620 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8619, uu____8620) in
                                      FStar_SMTEncoding_Util.mkSub uu____8616 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8615 in
                                  quant xy uu____8614 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8608) in
                              let uu____8626 =
                                let uu____8635 =
                                  let uu____8643 =
                                    let uu____8649 =
                                      let uu____8650 =
                                        let uu____8651 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8651 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8650 in
                                    quant qx uu____8649 in
                                  (FStar_Syntax_Const.op_Minus, uu____8643) in
                                let uu____8657 =
                                  let uu____8666 =
                                    let uu____8674 =
                                      let uu____8680 =
                                        let uu____8681 =
                                          let uu____8682 =
                                            let uu____8685 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8686 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8685, uu____8686) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8682 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8681 in
                                      quant xy uu____8680 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8674) in
                                  let uu____8692 =
                                    let uu____8701 =
                                      let uu____8709 =
                                        let uu____8715 =
                                          let uu____8716 =
                                            let uu____8717 =
                                              let uu____8720 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8721 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8720, uu____8721) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8717 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8716 in
                                        quant xy uu____8715 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8709) in
                                    let uu____8727 =
                                      let uu____8736 =
                                        let uu____8744 =
                                          let uu____8750 =
                                            let uu____8751 =
                                              let uu____8752 =
                                                let uu____8755 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8756 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8755, uu____8756) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8752 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8751 in
                                          quant xy uu____8750 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8744) in
                                      let uu____8762 =
                                        let uu____8771 =
                                          let uu____8779 =
                                            let uu____8785 =
                                              let uu____8786 =
                                                let uu____8787 =
                                                  let uu____8790 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8791 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8790, uu____8791) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8787 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8786 in
                                            quant xy uu____8785 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8779) in
                                        let uu____8797 =
                                          let uu____8806 =
                                            let uu____8814 =
                                              let uu____8820 =
                                                let uu____8821 =
                                                  let uu____8822 =
                                                    let uu____8825 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8826 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8825, uu____8826) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8822 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8821 in
                                              quant xy uu____8820 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8814) in
                                          let uu____8832 =
                                            let uu____8841 =
                                              let uu____8849 =
                                                let uu____8855 =
                                                  let uu____8856 =
                                                    let uu____8857 =
                                                      let uu____8860 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8861 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8860,
                                                        uu____8861) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8857 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8856 in
                                                quant xy uu____8855 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8849) in
                                            let uu____8867 =
                                              let uu____8876 =
                                                let uu____8884 =
                                                  let uu____8890 =
                                                    let uu____8891 =
                                                      let uu____8892 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8892 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8891 in
                                                  quant qx uu____8890 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8884) in
                                              [uu____8876] in
                                            uu____8841 :: uu____8867 in
                                          uu____8806 :: uu____8832 in
                                        uu____8771 :: uu____8797 in
                                      uu____8736 :: uu____8762 in
                                    uu____8701 :: uu____8727 in
                                  uu____8666 :: uu____8692 in
                                uu____8635 :: uu____8657 in
                              uu____8600 :: uu____8626 in
                            uu____8565 :: uu____8591 in
                          uu____8530 :: uu____8556 in
                        uu____8495 :: uu____8521 in
                      uu____8460 :: uu____8486 in
                    uu____8429 :: uu____8451 in
                  uu____8399 :: uu____8420 in
                let mk1 l v1 =
                  let uu____9020 =
                    let uu____9025 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9057  ->
                              match uu____9057 with
                              | (l',uu____9066) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____9025
                      (FStar_Option.map
                         (fun uu____9099  ->
                            match uu____9099 with | (uu____9110,b) -> b v1)) in
                  FStar_All.pipe_right uu____9020 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9151  ->
                          match uu____9151 with
                          | (l',uu____9160) -> FStar_Ident.lid_equals l l')) in
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
        let uu____9186 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____9186 with
        | (xxsym,xx) ->
            let uu____9191 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____9191 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____9199 =
                   let uu____9203 =
                     let uu____9204 =
                       let uu____9210 =
                         let uu____9211 =
                           let uu____9214 =
                             let uu____9215 =
                               let uu____9218 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____9218) in
                             FStar_SMTEncoding_Util.mkEq uu____9215 in
                           (xx_has_type, uu____9214) in
                         FStar_SMTEncoding_Util.mkImp uu____9211 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9210) in
                     FStar_SMTEncoding_Util.mkForall uu____9204 in
                   let uu____9231 =
                     let uu____9232 =
                       let uu____9233 =
                         let uu____9234 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____9234 in
                       Prims.strcat module_name uu____9233 in
                     varops.mk_unique uu____9232 in
                   (uu____9203, (Some "pretyping"), uu____9231) in
                 FStar_SMTEncoding_Util.mkAssume uu____9199)
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
    let uu____9264 =
      let uu____9265 =
        let uu____9269 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____9269, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9265 in
    let uu____9271 =
      let uu____9273 =
        let uu____9274 =
          let uu____9278 =
            let uu____9279 =
              let uu____9285 =
                let uu____9286 =
                  let uu____9289 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____9289) in
                FStar_SMTEncoding_Util.mkImp uu____9286 in
              ([[typing_pred]], [xx], uu____9285) in
            mkForall_fuel uu____9279 in
          (uu____9278, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9274 in
      [uu____9273] in
    uu____9264 :: uu____9271 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9317 =
      let uu____9318 =
        let uu____9322 =
          let uu____9323 =
            let uu____9329 =
              let uu____9332 =
                let uu____9334 = FStar_SMTEncoding_Term.boxBool b in
                [uu____9334] in
              [uu____9332] in
            let uu____9337 =
              let uu____9338 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____9338 tt in
            (uu____9329, [bb], uu____9337) in
          FStar_SMTEncoding_Util.mkForall uu____9323 in
        (uu____9322, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9318 in
    let uu____9349 =
      let uu____9351 =
        let uu____9352 =
          let uu____9356 =
            let uu____9357 =
              let uu____9363 =
                let uu____9364 =
                  let uu____9367 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____9367) in
                FStar_SMTEncoding_Util.mkImp uu____9364 in
              ([[typing_pred]], [xx], uu____9363) in
            mkForall_fuel uu____9357 in
          (uu____9356, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9352 in
      [uu____9351] in
    uu____9317 :: uu____9349 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____9401 =
        let uu____9402 =
          let uu____9406 =
            let uu____9408 =
              let uu____9410 =
                let uu____9412 = FStar_SMTEncoding_Term.boxInt a in
                let uu____9413 =
                  let uu____9415 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____9415] in
                uu____9412 :: uu____9413 in
              tt :: uu____9410 in
            tt :: uu____9408 in
          ("Prims.Precedes", uu____9406) in
        FStar_SMTEncoding_Util.mkApp uu____9402 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9401 in
    let precedes_y_x =
      let uu____9418 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9418 in
    let uu____9420 =
      let uu____9421 =
        let uu____9425 =
          let uu____9426 =
            let uu____9432 =
              let uu____9435 =
                let uu____9437 = FStar_SMTEncoding_Term.boxInt b in
                [uu____9437] in
              [uu____9435] in
            let uu____9440 =
              let uu____9441 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____9441 tt in
            (uu____9432, [bb], uu____9440) in
          FStar_SMTEncoding_Util.mkForall uu____9426 in
        (uu____9425, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9421 in
    let uu____9452 =
      let uu____9454 =
        let uu____9455 =
          let uu____9459 =
            let uu____9460 =
              let uu____9466 =
                let uu____9467 =
                  let uu____9470 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____9470) in
                FStar_SMTEncoding_Util.mkImp uu____9467 in
              ([[typing_pred]], [xx], uu____9466) in
            mkForall_fuel uu____9460 in
          (uu____9459, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9455 in
      let uu____9483 =
        let uu____9485 =
          let uu____9486 =
            let uu____9490 =
              let uu____9491 =
                let uu____9497 =
                  let uu____9498 =
                    let uu____9501 =
                      let uu____9502 =
                        let uu____9504 =
                          let uu____9506 =
                            let uu____9508 =
                              let uu____9509 =
                                let uu____9512 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____9513 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____9512, uu____9513) in
                              FStar_SMTEncoding_Util.mkGT uu____9509 in
                            let uu____9514 =
                              let uu____9516 =
                                let uu____9517 =
                                  let uu____9520 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____9521 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____9520, uu____9521) in
                                FStar_SMTEncoding_Util.mkGTE uu____9517 in
                              let uu____9522 =
                                let uu____9524 =
                                  let uu____9525 =
                                    let uu____9528 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____9529 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____9528, uu____9529) in
                                  FStar_SMTEncoding_Util.mkLT uu____9525 in
                                [uu____9524] in
                              uu____9516 :: uu____9522 in
                            uu____9508 :: uu____9514 in
                          typing_pred_y :: uu____9506 in
                        typing_pred :: uu____9504 in
                      FStar_SMTEncoding_Util.mk_and_l uu____9502 in
                    (uu____9501, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____9498 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9497) in
              mkForall_fuel uu____9491 in
            (uu____9490, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____9486 in
        [uu____9485] in
      uu____9454 :: uu____9483 in
    uu____9420 :: uu____9452 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____9559 =
      let uu____9560 =
        let uu____9564 =
          let uu____9565 =
            let uu____9571 =
              let uu____9574 =
                let uu____9576 = FStar_SMTEncoding_Term.boxString b in
                [uu____9576] in
              [uu____9574] in
            let uu____9579 =
              let uu____9580 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9580 tt in
            (uu____9571, [bb], uu____9579) in
          FStar_SMTEncoding_Util.mkForall uu____9565 in
        (uu____9564, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____9560 in
    let uu____9591 =
      let uu____9593 =
        let uu____9594 =
          let uu____9598 =
            let uu____9599 =
              let uu____9605 =
                let uu____9606 =
                  let uu____9609 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9609) in
                FStar_SMTEncoding_Util.mkImp uu____9606 in
              ([[typing_pred]], [xx], uu____9605) in
            mkForall_fuel uu____9599 in
          (uu____9598, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9594 in
      [uu____9593] in
    uu____9559 :: uu____9591 in
  let mk_ref1 env reft_name uu____9631 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9642 =
        let uu____9646 =
          let uu____9648 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9648] in
        (reft_name, uu____9646) in
      FStar_SMTEncoding_Util.mkApp uu____9642 in
    let refb =
      let uu____9651 =
        let uu____9655 =
          let uu____9657 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9657] in
        (reft_name, uu____9655) in
      FStar_SMTEncoding_Util.mkApp uu____9651 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9661 =
      let uu____9662 =
        let uu____9666 =
          let uu____9667 =
            let uu____9673 =
              let uu____9674 =
                let uu____9677 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9677) in
              FStar_SMTEncoding_Util.mkImp uu____9674 in
            ([[typing_pred]], [xx; aa], uu____9673) in
          mkForall_fuel uu____9667 in
        (uu____9666, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9662 in
    [uu____9661] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9717 =
      let uu____9718 =
        let uu____9722 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9722, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9718 in
    [uu____9717] in
  let mk_and_interp env conj uu____9733 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9750 =
      let uu____9751 =
        let uu____9755 =
          let uu____9756 =
            let uu____9762 =
              let uu____9763 =
                let uu____9766 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9766, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9763 in
            ([[l_and_a_b]], [aa; bb], uu____9762) in
          FStar_SMTEncoding_Util.mkForall uu____9756 in
        (uu____9755, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9751 in
    [uu____9750] in
  let mk_or_interp env disj uu____9790 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9807 =
      let uu____9808 =
        let uu____9812 =
          let uu____9813 =
            let uu____9819 =
              let uu____9820 =
                let uu____9823 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9823, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9820 in
            ([[l_or_a_b]], [aa; bb], uu____9819) in
          FStar_SMTEncoding_Util.mkForall uu____9813 in
        (uu____9812, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9808 in
    [uu____9807] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9864 =
      let uu____9865 =
        let uu____9869 =
          let uu____9870 =
            let uu____9876 =
              let uu____9877 =
                let uu____9880 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9880, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9877 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9876) in
          FStar_SMTEncoding_Util.mkForall uu____9870 in
        (uu____9869, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9865 in
    [uu____9864] in
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
    let uu____9927 =
      let uu____9928 =
        let uu____9932 =
          let uu____9933 =
            let uu____9939 =
              let uu____9940 =
                let uu____9943 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9943, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9940 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9939) in
          FStar_SMTEncoding_Util.mkForall uu____9933 in
        (uu____9932, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9928 in
    [uu____9927] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9988 =
      let uu____9989 =
        let uu____9993 =
          let uu____9994 =
            let uu____10000 =
              let uu____10001 =
                let uu____10004 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____10004, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10001 in
            ([[l_imp_a_b]], [aa; bb], uu____10000) in
          FStar_SMTEncoding_Util.mkForall uu____9994 in
        (uu____9993, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9989 in
    [uu____9988] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____10045 =
      let uu____10046 =
        let uu____10050 =
          let uu____10051 =
            let uu____10057 =
              let uu____10058 =
                let uu____10061 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____10061, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10058 in
            ([[l_iff_a_b]], [aa; bb], uu____10057) in
          FStar_SMTEncoding_Util.mkForall uu____10051 in
        (uu____10050, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10046 in
    [uu____10045] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____10095 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10095 in
    let uu____10097 =
      let uu____10098 =
        let uu____10102 =
          let uu____10103 =
            let uu____10109 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____10109) in
          FStar_SMTEncoding_Util.mkForall uu____10103 in
        (uu____10102, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10098 in
    [uu____10097] in
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
      let uu____10149 =
        let uu____10153 =
          let uu____10155 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10155] in
        ("Valid", uu____10153) in
      FStar_SMTEncoding_Util.mkApp uu____10149 in
    let uu____10157 =
      let uu____10158 =
        let uu____10162 =
          let uu____10163 =
            let uu____10169 =
              let uu____10170 =
                let uu____10173 =
                  let uu____10174 =
                    let uu____10180 =
                      let uu____10183 =
                        let uu____10185 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10185] in
                      [uu____10183] in
                    let uu____10188 =
                      let uu____10189 =
                        let uu____10192 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10192, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10189 in
                    (uu____10180, [xx1], uu____10188) in
                  FStar_SMTEncoding_Util.mkForall uu____10174 in
                (uu____10173, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10170 in
            ([[l_forall_a_b]], [aa; bb], uu____10169) in
          FStar_SMTEncoding_Util.mkForall uu____10163 in
        (uu____10162, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10158 in
    [uu____10157] in
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
      let uu____10243 =
        let uu____10247 =
          let uu____10249 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____10249] in
        ("Valid", uu____10247) in
      FStar_SMTEncoding_Util.mkApp uu____10243 in
    let uu____10251 =
      let uu____10252 =
        let uu____10256 =
          let uu____10257 =
            let uu____10263 =
              let uu____10264 =
                let uu____10267 =
                  let uu____10268 =
                    let uu____10274 =
                      let uu____10277 =
                        let uu____10279 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____10279] in
                      [uu____10277] in
                    let uu____10282 =
                      let uu____10283 =
                        let uu____10286 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____10286, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____10283 in
                    (uu____10274, [xx1], uu____10282) in
                  FStar_SMTEncoding_Util.mkExists uu____10268 in
                (uu____10267, valid) in
              FStar_SMTEncoding_Util.mkIff uu____10264 in
            ([[l_exists_a_b]], [aa; bb], uu____10263) in
          FStar_SMTEncoding_Util.mkForall uu____10257 in
        (uu____10256, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____10252 in
    [uu____10251] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____10322 =
      let uu____10323 =
        let uu____10327 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____10328 = varops.mk_unique "typing_range_const" in
        (uu____10327, (Some "Range_const typing"), uu____10328) in
      FStar_SMTEncoding_Util.mkAssume uu____10323 in
    [uu____10322] in
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
          let uu____10590 =
            FStar_Util.find_opt
              (fun uu____10608  ->
                 match uu____10608 with
                 | (l,uu____10618) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10590 with
          | None  -> []
          | Some (uu____10640,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10677 = encode_function_type_as_formula t env in
        match uu____10677 with
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
            let uu____10709 =
              (let uu____10710 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10710) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10709
            then
              let uu____10714 = new_term_constant_and_tok_from_lid env lid in
              match uu____10714 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10726 =
                      let uu____10727 = FStar_Syntax_Subst.compress t_norm in
                      uu____10727.FStar_Syntax_Syntax.n in
                    match uu____10726 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10732) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10749  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10752 -> [] in
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
              (let uu____10761 = prims.is lid in
               if uu____10761
               then
                 let vname = varops.new_fvar lid in
                 let uu____10766 = prims.mk lid vname in
                 match uu____10766 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10781 =
                    let uu____10787 = curried_arrow_formals_comp t_norm in
                    match uu____10787 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10798 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10798
                          then
                            let uu____10799 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10800 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10800.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10800.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10800.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10800.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10800.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10800.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10800.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10800.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10800.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10800.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10800.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10800.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10800.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10800.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10800.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10800.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10800.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10800.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10800.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10800.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10800.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10800.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10800.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10800.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10800.FStar_TypeChecker_Env.synth)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10799
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10807 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10807)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10781 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10834 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10834 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10847 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___114_10871  ->
                                     match uu___114_10871 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10874 =
                                           FStar_Util.prefix vars in
                                         (match uu____10874 with
                                          | (uu____10885,(xxsym,uu____10887))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10897 =
                                                let uu____10898 =
                                                  let uu____10902 =
                                                    let uu____10903 =
                                                      let uu____10909 =
                                                        let uu____10910 =
                                                          let uu____10913 =
                                                            let uu____10914 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10914 in
                                                          (vapp, uu____10913) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10910 in
                                                      ([[vapp]], vars,
                                                        uu____10909) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10903 in
                                                  (uu____10902,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10898 in
                                              [uu____10897])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10925 =
                                           FStar_Util.prefix vars in
                                         (match uu____10925 with
                                          | (uu____10936,(xxsym,uu____10938))
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
                                              let uu____10952 =
                                                let uu____10953 =
                                                  let uu____10957 =
                                                    let uu____10958 =
                                                      let uu____10964 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10964) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10958 in
                                                  (uu____10957,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10953 in
                                              [uu____10952])
                                     | uu____10973 -> [])) in
                           let uu____10974 = encode_binders None formals env1 in
                           (match uu____10974 with
                            | (vars,guards,env',decls1,uu____10990) ->
                                let uu____10997 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____11002 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____11002, decls1)
                                  | Some p ->
                                      let uu____11004 = encode_formula p env' in
                                      (match uu____11004 with
                                       | (g,ds) ->
                                           let uu____11011 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____11011,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10997 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____11020 =
                                         let uu____11024 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____11024) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____11020 in
                                     let uu____11029 =
                                       let vname_decl =
                                         let uu____11034 =
                                           let uu____11040 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11045  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____11040,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____11034 in
                                       let uu____11050 =
                                         let env2 =
                                           let uu___144_11054 = env1 in
                                           {
                                             bindings =
                                               (uu___144_11054.bindings);
                                             depth = (uu___144_11054.depth);
                                             tcenv = (uu___144_11054.tcenv);
                                             warn = (uu___144_11054.warn);
                                             cache = (uu___144_11054.cache);
                                             nolabels =
                                               (uu___144_11054.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11054.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11054.current_module_name)
                                           } in
                                         let uu____11055 =
                                           let uu____11056 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____11056 in
                                         if uu____11055
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____11050 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11066::uu____11067 ->
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
                                                   let uu____11090 =
                                                     let uu____11096 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11096) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11090 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11110 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____11112 =
                                             match formals with
                                             | [] ->
                                                 let uu____11121 =
                                                   let uu____11122 =
                                                     let uu____11124 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_44  ->
                                                          Some _0_44)
                                                       uu____11124 in
                                                   push_free_var env1 lid
                                                     vname uu____11122 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11121)
                                             | uu____11127 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____11132 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11132 in
                                                 let name_tok_corr =
                                                   let uu____11134 =
                                                     let uu____11138 =
                                                       let uu____11139 =
                                                         let uu____11145 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11145) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11139 in
                                                     (uu____11138,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11134 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____11112 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____11029 with
                                      | (decls2,env2) ->
                                          let uu____11169 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____11174 =
                                              encode_term res_t1 env' in
                                            match uu____11174 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11182 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____11182,
                                                  decls) in
                                          (match uu____11169 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11190 =
                                                   let uu____11194 =
                                                     let uu____11195 =
                                                       let uu____11201 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____11201) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11195 in
                                                   (uu____11194,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11190 in
                                               let freshness =
                                                 let uu____11210 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____11210
                                                 then
                                                   let uu____11213 =
                                                     let uu____11214 =
                                                       let uu____11220 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____11226 =
                                                         varops.next_id () in
                                                       (vname, uu____11220,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11226) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11214 in
                                                   let uu____11228 =
                                                     let uu____11230 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____11230] in
                                                   uu____11213 :: uu____11228
                                                 else [] in
                                               let g =
                                                 let uu____11234 =
                                                   let uu____11236 =
                                                     let uu____11238 =
                                                       let uu____11240 =
                                                         let uu____11242 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____11242 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11240 in
                                                     FStar_List.append decls3
                                                       uu____11238 in
                                                   FStar_List.append decls2
                                                     uu____11236 in
                                                 FStar_List.append decls11
                                                   uu____11234 in
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
          let uu____11264 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____11264 with
          | None  ->
              let uu____11287 = encode_free_var env x t t_norm [] in
              (match uu____11287 with
               | (decls,env1) ->
                   let uu____11302 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____11302 with
                    | (n1,x',uu____11321) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____11333) -> ((n1, x1), [], env)
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
          let uu____11366 = encode_free_var env lid t tt quals in
          match uu____11366 with
          | (decls,env1) ->
              let uu____11377 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____11377
              then
                let uu____11381 =
                  let uu____11383 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____11383 in
                (uu____11381, env1)
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
             (fun uu____11411  ->
                fun lb  ->
                  match uu____11411 with
                  | (decls,env1) ->
                      let uu____11423 =
                        let uu____11427 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____11427
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____11423 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____11441 = FStar_Syntax_Util.head_and_args t in
    match uu____11441 with
    | (hd1,args) ->
        let uu____11467 =
          let uu____11468 = FStar_Syntax_Util.un_uinst hd1 in
          uu____11468.FStar_Syntax_Syntax.n in
        (match uu____11467 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11472,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11485 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____11500  ->
      fun quals  ->
        match uu____11500 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____11550 = FStar_Util.first_N nbinders formals in
              match uu____11550 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11592  ->
                         fun uu____11593  ->
                           match (uu____11592, uu____11593) with
                           | ((formal,uu____11603),(binder,uu____11605)) ->
                               let uu____11610 =
                                 let uu____11615 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11615) in
                               FStar_Syntax_Syntax.NT uu____11610) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11620 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11634  ->
                              match uu____11634 with
                              | (x,i) ->
                                  let uu____11641 =
                                    let uu___145_11642 = x in
                                    let uu____11643 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11642.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11642.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11643
                                    } in
                                  (uu____11641, i))) in
                    FStar_All.pipe_right uu____11620
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11655 =
                      let uu____11657 =
                        let uu____11658 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11658.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_45  -> Some _0_45)
                        uu____11657 in
                    let uu____11662 =
                      let uu____11663 = FStar_Syntax_Subst.compress body in
                      let uu____11664 =
                        let uu____11665 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11665 in
                      FStar_Syntax_Syntax.extend_app_n uu____11663
                        uu____11664 in
                    uu____11662 uu____11655 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11707 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11707
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11708 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11708.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11708.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11708.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11708.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11708.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11708.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11708.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11708.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11708.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11708.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11708.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11708.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11708.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11708.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11708.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11708.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11708.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11708.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11708.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11708.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11708.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11708.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11708.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11708.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11708.FStar_TypeChecker_Env.synth)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11729 = FStar_Syntax_Util.abs_formals e in
                match uu____11729 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11778::uu____11779 ->
                         let uu____11787 =
                           let uu____11788 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11788.FStar_Syntax_Syntax.n in
                         (match uu____11787 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11815 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11815 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11843 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11843
                                   then
                                     let uu____11866 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11866 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11914  ->
                                                   fun uu____11915  ->
                                                     match (uu____11914,
                                                             uu____11915)
                                                     with
                                                     | ((x,uu____11925),
                                                        (b,uu____11927)) ->
                                                         let uu____11932 =
                                                           let uu____11937 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11937) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11932)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11939 =
                                            let uu____11950 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11950) in
                                          (uu____11939, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11990 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11990 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12042) ->
                              let uu____12047 =
                                let uu____12058 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____12058 in
                              (uu____12047, true)
                          | uu____12091 when Prims.op_Negation norm1 ->
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
                          | uu____12093 ->
                              let uu____12094 =
                                let uu____12095 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____12096 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12095
                                  uu____12096 in
                              failwith uu____12094)
                     | uu____12109 ->
                         let uu____12110 =
                           let uu____12111 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____12111.FStar_Syntax_Syntax.n in
                         (match uu____12110 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12138 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____12138 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____12156 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____12156 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12204 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____12232 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____12232
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12239 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____12280  ->
                            fun lb  ->
                              match uu____12280 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____12331 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____12331
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____12334 =
                                      let uu____12342 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____12342
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____12334 with
                                    | (tok,decl,env2) ->
                                        let uu____12367 =
                                          let uu____12374 =
                                            let uu____12380 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____12380, tok) in
                                          uu____12374 :: toks in
                                        (uu____12367, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____12239 with
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
                        | uu____12482 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____12487 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____12487 vars)
                            else
                              (let uu____12489 =
                                 let uu____12493 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____12493) in
                               FStar_SMTEncoding_Util.mkApp uu____12489) in
                      let uu____12498 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___115_12500  ->
                                 match uu___115_12500 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12501 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12504 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12504))) in
                      if uu____12498
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12524;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12526;
                                FStar_Syntax_Syntax.lbeff = uu____12527;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____12568 =
                                 let uu____12572 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____12572 with
                                 | (tcenv',uu____12583,e_t) ->
                                     let uu____12587 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12594 -> failwith "Impossible" in
                                     (match uu____12587 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12603 = env1 in
                                            {
                                              bindings =
                                                (uu___149_12603.bindings);
                                              depth = (uu___149_12603.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12603.warn);
                                              cache = (uu___149_12603.cache);
                                              nolabels =
                                                (uu___149_12603.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12603.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12603.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12603.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____12568 with
                                | (env',e1,t_norm1) ->
                                    let uu____12610 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12610 with
                                     | ((binders,body,uu____12622,uu____12623),curry)
                                         ->
                                         ((let uu____12630 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12630
                                           then
                                             let uu____12631 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12632 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12631 uu____12632
                                           else ());
                                          (let uu____12634 =
                                             encode_binders None binders env' in
                                           match uu____12634 with
                                           | (vars,guards,env'1,binder_decls,uu____12650)
                                               ->
                                               let body1 =
                                                 let uu____12658 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12658
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12661 =
                                                 let uu____12666 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12666
                                                 then
                                                   let uu____12672 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12673 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12672, uu____12673)
                                                 else
                                                   (let uu____12679 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12679)) in
                                               (match uu____12661 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12693 =
                                                        let uu____12697 =
                                                          let uu____12698 =
                                                            let uu____12704 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12704) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12698 in
                                                        let uu____12710 =
                                                          let uu____12712 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12712 in
                                                        (uu____12697,
                                                          uu____12710,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12693 in
                                                    let uu____12714 =
                                                      let uu____12716 =
                                                        let uu____12718 =
                                                          let uu____12720 =
                                                            let uu____12722 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12722 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12720 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12718 in
                                                      FStar_List.append
                                                        decls1 uu____12716 in
                                                    (uu____12714, env1))))))
                           | uu____12725 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12744 = varops.fresh "fuel" in
                             (uu____12744, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12747 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12786  ->
                                     fun uu____12787  ->
                                       match (uu____12786, uu____12787) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12869 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12869 in
                                           let gtok =
                                             let uu____12871 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12871 in
                                           let env3 =
                                             let uu____12873 =
                                               let uu____12875 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_46  -> Some _0_46)
                                                 uu____12875 in
                                             push_free_var env2 flid gtok
                                               uu____12873 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12747 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12961
                                 t_norm uu____12963 =
                                 match (uu____12961, uu____12963) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12990;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12991;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____13008 =
                                       let uu____13012 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____13012 with
                                       | (tcenv',uu____13027,e_t) ->
                                           let uu____13031 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13038 ->
                                                 failwith "Impossible" in
                                           (match uu____13031 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13047 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___150_13047.bindings);
                                                    depth =
                                                      (uu___150_13047.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13047.warn);
                                                    cache =
                                                      (uu___150_13047.cache);
                                                    nolabels =
                                                      (uu___150_13047.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13047.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13047.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13047.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____13008 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13057 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____13057
                                            then
                                              let uu____13058 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____13059 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____13060 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13058 uu____13059
                                                uu____13060
                                            else ());
                                           (let uu____13062 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____13062 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13084 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____13084
                                                  then
                                                    let uu____13085 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____13086 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____13087 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____13088 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13085 uu____13086
                                                      uu____13087 uu____13088
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13092 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____13092 with
                                                  | (vars,guards,env'1,binder_decls,uu____13110)
                                                      ->
                                                      let decl_g =
                                                        let uu____13118 =
                                                          let uu____13124 =
                                                            let uu____13126 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13126 in
                                                          (g, uu____13124,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13118 in
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
                                                        let uu____13141 =
                                                          let uu____13145 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____13145) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13141 in
                                                      let gsapp =
                                                        let uu____13151 =
                                                          let uu____13155 =
                                                            let uu____13157 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____13157 ::
                                                              vars_tm in
                                                          (g, uu____13155) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13151 in
                                                      let gmax =
                                                        let uu____13161 =
                                                          let uu____13165 =
                                                            let uu____13167 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____13167 ::
                                                              vars_tm in
                                                          (g, uu____13165) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13161 in
                                                      let body1 =
                                                        let uu____13171 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____13171
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____13173 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____13173 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13184
                                                               =
                                                               let uu____13188
                                                                 =
                                                                 let uu____13189
                                                                   =
                                                                   let uu____13197
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
                                                                    uu____13197) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13189 in
                                                               let uu____13208
                                                                 =
                                                                 let uu____13210
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____13210 in
                                                               (uu____13188,
                                                                 uu____13208,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13184 in
                                                           let eqn_f =
                                                             let uu____13213
                                                               =
                                                               let uu____13217
                                                                 =
                                                                 let uu____13218
                                                                   =
                                                                   let uu____13224
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13224) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13218 in
                                                               (uu____13217,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13213 in
                                                           let eqn_g' =
                                                             let uu____13232
                                                               =
                                                               let uu____13236
                                                                 =
                                                                 let uu____13237
                                                                   =
                                                                   let uu____13243
                                                                    =
                                                                    let uu____13244
                                                                    =
                                                                    let uu____13247
                                                                    =
                                                                    let uu____13248
                                                                    =
                                                                    let uu____13252
                                                                    =
                                                                    let uu____13254
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____13254
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____13252) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13248 in
                                                                    (gsapp,
                                                                    uu____13247) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13244 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13243) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13237 in
                                                               (uu____13236,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13232 in
                                                           let uu____13266 =
                                                             let uu____13271
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____13271
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____13288)
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
                                                                    let uu____13303
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____13303
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____13306
                                                                    =
                                                                    let uu____13310
                                                                    =
                                                                    let uu____13311
                                                                    =
                                                                    let uu____13317
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13317) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13311 in
                                                                    (uu____13310,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13306 in
                                                                 let uu____13328
                                                                   =
                                                                   let uu____13332
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____13332
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____13340
                                                                    =
                                                                    let uu____13342
                                                                    =
                                                                    let uu____13343
                                                                    =
                                                                    let uu____13347
                                                                    =
                                                                    let uu____13348
                                                                    =
                                                                    let uu____13354
                                                                    =
                                                                    let uu____13355
                                                                    =
                                                                    let uu____13358
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____13358,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13355 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13354) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13348 in
                                                                    (uu____13347,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13343 in
                                                                    [uu____13342] in
                                                                    (d3,
                                                                    uu____13340) in
                                                                 (match uu____13328
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____13266
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
                               let uu____13393 =
                                 let uu____13400 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____13436  ->
                                      fun uu____13437  ->
                                        match (uu____13436, uu____13437) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13523 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____13523 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13400 in
                               (match uu____13393 with
                                | (decls2,eqns,env01) ->
                                    let uu____13563 =
                                      let isDeclFun uu___116_13571 =
                                        match uu___116_13571 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13572 -> true
                                        | uu____13578 -> false in
                                      let uu____13579 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____13579
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____13563 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13606 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13606
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
        let uu____13639 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13639 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13642 = encode_sigelt' env se in
      match uu____13642 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13652 =
                  let uu____13653 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13653 in
                [uu____13652]
            | uu____13654 ->
                let uu____13655 =
                  let uu____13657 =
                    let uu____13658 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13658 in
                  uu____13657 :: g in
                let uu____13659 =
                  let uu____13661 =
                    let uu____13662 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13662 in
                  [uu____13661] in
                FStar_List.append uu____13655 uu____13659 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13672 =
          let uu____13673 = FStar_Syntax_Subst.compress t in
          uu____13673.FStar_Syntax_Syntax.n in
        match uu____13672 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13677)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13680 -> false in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13683 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13686 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13688 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13690 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13698 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13701 =
            let uu____13702 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13702 Prims.op_Negation in
          if uu____13701
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13722 ->
                   let uu____13723 =
                     let uu____13726 =
                       let uu____13727 =
                         let uu____13742 =
                           FStar_All.pipe_left (fun _0_47  -> Some _0_47)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13742) in
                       FStar_Syntax_Syntax.Tm_abs uu____13727 in
                     FStar_Syntax_Syntax.mk uu____13726 in
                   uu____13723 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13795 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13795 with
               | (aname,atok,env2) ->
                   let uu____13805 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13805 with
                    | (formals,uu____13815) ->
                        let uu____13822 =
                          let uu____13825 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13825 env2 in
                        (match uu____13822 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13833 =
                                 let uu____13834 =
                                   let uu____13840 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13848  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13840,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13834 in
                               [uu____13833;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13855 =
                               let aux uu____13884 uu____13885 =
                                 match (uu____13884, uu____13885) with
                                 | ((bv,uu____13912),(env3,acc_sorts,acc)) ->
                                     let uu____13933 = gen_term_var env3 bv in
                                     (match uu____13933 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13855 with
                              | (uu____13971,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13985 =
                                      let uu____13989 =
                                        let uu____13990 =
                                          let uu____13996 =
                                            let uu____13997 =
                                              let uu____14000 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____14000) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13997 in
                                          ([[app]], xs_sorts, uu____13996) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13990 in
                                      (uu____13989, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13985 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____14012 =
                                      let uu____14016 =
                                        let uu____14017 =
                                          let uu____14023 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____14023) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____14017 in
                                      (uu____14016,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____14012 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____14033 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____14033 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14049,uu____14050)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____14051 = new_term_constant_and_tok_from_lid env lid in
          (match uu____14051 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____14062,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____14067 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___117_14069  ->
                      match uu___117_14069 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____14070 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____14073 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____14074 -> false)) in
            Prims.op_Negation uu____14067 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____14080 = encode_top_level_val env fv t quals in
             match uu____14080 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____14092 =
                   let uu____14094 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____14094 in
                 (uu____14092, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____14099 = encode_formula f env in
          (match uu____14099 with
           | (f1,decls) ->
               let g =
                 let uu____14108 =
                   let uu____14109 =
                     let uu____14113 =
                       let uu____14115 =
                         let uu____14116 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____14116 in
                       Some uu____14115 in
                     let uu____14117 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____14113, uu____14117) in
                   FStar_SMTEncoding_Util.mkAssume uu____14109 in
                 [uu____14108] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14121,attrs) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right attrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let uu____14129 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14136 =
                       let uu____14141 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____14141.FStar_Syntax_Syntax.fv_name in
                     uu____14136.FStar_Syntax_Syntax.v in
                   let uu____14145 =
                     let uu____14146 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____14146 in
                   if uu____14145
                   then
                     let val_decl =
                       let uu___151_14161 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14161.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14161.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____14165 = encode_sigelt' env1 val_decl in
                     match uu____14165 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____14129 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14182,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14184;
                          FStar_Syntax_Syntax.lbtyp = uu____14185;
                          FStar_Syntax_Syntax.lbeff = uu____14186;
                          FStar_Syntax_Syntax.lbdef = uu____14187;_}::[]),uu____14188,uu____14189)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____14203 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____14203 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____14226 =
                   let uu____14228 =
                     let uu____14229 =
                       let uu____14233 =
                         let uu____14234 =
                           let uu____14240 =
                             let uu____14241 =
                               let uu____14244 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____14244) in
                             FStar_SMTEncoding_Util.mkEq uu____14241 in
                           ([[b2t_x]], [xx], uu____14240) in
                         FStar_SMTEncoding_Util.mkForall uu____14234 in
                       (uu____14233, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____14229 in
                   [uu____14228] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____14226 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14261,uu____14262,uu____14263)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___118_14269  ->
                  match uu___118_14269 with
                  | FStar_Syntax_Syntax.Discriminator uu____14270 -> true
                  | uu____14271 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14273,lids,uu____14275) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14282 =
                     let uu____14283 = FStar_List.hd l.FStar_Ident.ns in
                     uu____14283.FStar_Ident.idText in
                   uu____14282 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___119_14285  ->
                     match uu___119_14285 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14286 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14289,uu____14290)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_14300  ->
                  match uu___120_14300 with
                  | FStar_Syntax_Syntax.Projector uu____14301 -> true
                  | uu____14304 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____14311 = try_lookup_free_var env l in
          (match uu____14311 with
           | Some uu____14315 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_14318 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_14318.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_14318.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____14324,uu____14325) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14337) ->
          let uu____14342 = encode_sigelts env ses in
          (match uu____14342 with
           | (g,env1) ->
               let uu____14352 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___121_14362  ->
                         match uu___121_14362 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____14363;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____14364;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____14365;_}
                             -> false
                         | uu____14367 -> true)) in
               (match uu____14352 with
                | (g',inversions) ->
                    let uu____14376 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___122_14386  ->
                              match uu___122_14386 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14387 ->
                                  true
                              | uu____14393 -> false)) in
                    (match uu____14376 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____14404,tps,k,uu____14407,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___123_14417  ->
                    match uu___123_14417 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14418 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14425 = c in
              match uu____14425 with
              | (name,args,uu____14429,uu____14430,uu____14431) ->
                  let uu____14434 =
                    let uu____14435 =
                      let uu____14441 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14448  ->
                                match uu____14448 with
                                | (uu____14452,sort,uu____14454) -> sort)) in
                      (name, uu____14441, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____14435 in
                  [uu____14434]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____14472 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14475 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____14475 FStar_Option.isNone)) in
            if uu____14472
            then []
            else
              (let uu____14492 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____14492 with
               | (xxsym,xx) ->
                   let uu____14498 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14509  ->
                             fun l  ->
                               match uu____14509 with
                               | (out,decls) ->
                                   let uu____14521 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____14521 with
                                    | (uu____14527,data_t) ->
                                        let uu____14529 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____14529 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14558 =
                                                 let uu____14559 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____14559.FStar_Syntax_Syntax.n in
                                               match uu____14558 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14567,indices) ->
                                                   indices
                                               | uu____14583 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14595  ->
                                                         match uu____14595
                                                         with
                                                         | (x,uu____14599) ->
                                                             let uu____14600
                                                               =
                                                               let uu____14601
                                                                 =
                                                                 let uu____14605
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14605,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14601 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14600)
                                                    env) in
                                             let uu____14607 =
                                               encode_args indices env1 in
                                             (match uu____14607 with
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
                                                      let uu____14631 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14639
                                                                 =
                                                                 let uu____14642
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14642,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14639)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14631
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14644 =
                                                      let uu____14645 =
                                                        let uu____14648 =
                                                          let uu____14649 =
                                                            let uu____14652 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14652,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14649 in
                                                        (out, uu____14648) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14645 in
                                                    (uu____14644,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____14498 with
                    | (data_ax,decls) ->
                        let uu____14660 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14660 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14674 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14674 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14677 =
                                 let uu____14681 =
                                   let uu____14682 =
                                     let uu____14688 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14696 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14688,
                                       uu____14696) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14682 in
                                 let uu____14704 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14681, (Some "inversion axiom"),
                                   uu____14704) in
                               FStar_SMTEncoding_Util.mkAssume uu____14677 in
                             let pattern_guarded_inversion =
                               let uu____14708 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14708
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14719 =
                                   let uu____14720 =
                                     let uu____14724 =
                                       let uu____14725 =
                                         let uu____14731 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14739 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14731, uu____14739) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14725 in
                                     let uu____14747 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14724, (Some "inversion axiom"),
                                       uu____14747) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14720 in
                                 [uu____14719]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14750 =
            let uu____14758 =
              let uu____14759 = FStar_Syntax_Subst.compress k in
              uu____14759.FStar_Syntax_Syntax.n in
            match uu____14758 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14788 -> (tps, k) in
          (match uu____14750 with
           | (formals,res) ->
               let uu____14803 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14803 with
                | (formals1,res1) ->
                    let uu____14810 = encode_binders None formals1 env in
                    (match uu____14810 with
                     | (vars,guards,env',binder_decls,uu____14825) ->
                         let uu____14832 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14832 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14845 =
                                  let uu____14849 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14849) in
                                FStar_SMTEncoding_Util.mkApp uu____14845 in
                              let uu____14854 =
                                let tname_decl =
                                  let uu____14860 =
                                    let uu____14861 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14876  ->
                                              match uu____14876 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14884 = varops.next_id () in
                                    (tname, uu____14861,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14884, false) in
                                  constructor_or_logic_type_decl uu____14860 in
                                let uu____14889 =
                                  match vars with
                                  | [] ->
                                      let uu____14896 =
                                        let uu____14897 =
                                          let uu____14899 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_48  -> Some _0_48)
                                            uu____14899 in
                                        push_free_var env1 t tname
                                          uu____14897 in
                                      ([], uu____14896)
                                  | uu____14903 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14909 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14909 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14918 =
                                          let uu____14922 =
                                            let uu____14923 =
                                              let uu____14931 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14931) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14923 in
                                          (uu____14922,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14918 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14889 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14854 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14954 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14954 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14971 =
                                               let uu____14972 =
                                                 let uu____14976 =
                                                   let uu____14977 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14977 in
                                                 (uu____14976,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14972 in
                                             [uu____14971]
                                           else [] in
                                         let uu____14980 =
                                           let uu____14982 =
                                             let uu____14984 =
                                               let uu____14985 =
                                                 let uu____14989 =
                                                   let uu____14990 =
                                                     let uu____14996 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14996) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14990 in
                                                 (uu____14989, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14985 in
                                             [uu____14984] in
                                           FStar_List.append karr uu____14982 in
                                         FStar_List.append decls1 uu____14980 in
                                   let aux =
                                     let uu____15005 =
                                       let uu____15007 =
                                         inversion_axioms tapp vars in
                                       let uu____15009 =
                                         let uu____15011 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____15011] in
                                       FStar_List.append uu____15007
                                         uu____15009 in
                                     FStar_List.append kindingAx uu____15005 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15016,uu____15017,uu____15018,uu____15019,uu____15020)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____15025,t,uu____15027,n_tps,uu____15029) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____15034 = new_term_constant_and_tok_from_lid env d in
          (match uu____15034 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____15045 = FStar_Syntax_Util.arrow_formals t in
               (match uu____15045 with
                | (formals,t_res) ->
                    let uu____15067 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____15067 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____15076 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____15076 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____15114 =
                                            mk_term_projector_name d x in
                                          (uu____15114,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____15116 =
                                  let uu____15126 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15126, true) in
                                FStar_All.pipe_right uu____15116
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
                              let uu____15148 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____15148 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15156::uu____15157 ->
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
                                         let uu____15182 =
                                           let uu____15188 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15188) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15182
                                     | uu____15201 -> tok_typing in
                                   let uu____15206 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____15206 with
                                    | (vars',guards',env'',decls_formals,uu____15221)
                                        ->
                                        let uu____15228 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____15228 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15247 ->
                                                   let uu____15251 =
                                                     let uu____15252 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15252 in
                                                   [uu____15251] in
                                             let encode_elim uu____15259 =
                                               let uu____15260 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____15260 with
                                               | (head1,args) ->
                                                   let uu____15289 =
                                                     let uu____15290 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____15290.FStar_Syntax_Syntax.n in
                                                   (match uu____15289 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____15297;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____15298;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____15299;_},uu____15300)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15310 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15310
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
                                                                 | uu____15336
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15344
                                                                    =
                                                                    let uu____15345
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15345 in
                                                                    if
                                                                    uu____15344
                                                                    then
                                                                    let uu____15352
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15352]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15354
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15367
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15367
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15389
                                                                    =
                                                                    let uu____15393
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15393 in
                                                                    (match uu____15389
                                                                    with
                                                                    | 
                                                                    (uu____15400,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15406
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15406
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15408
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15408
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
                                                             (match uu____15354
                                                              with
                                                              | (uu____15416,arg_vars,elim_eqns_or_guards,uu____15419)
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
                                                                    let uu____15438
                                                                    =
                                                                    let uu____15442
                                                                    =
                                                                    let uu____15443
                                                                    =
                                                                    let uu____15449
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15455
                                                                    =
                                                                    let uu____15456
                                                                    =
                                                                    let uu____15459
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15459) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15456 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15449,
                                                                    uu____15455) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15443 in
                                                                    (uu____15442,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15438 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15472
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15472,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15474
                                                                    =
                                                                    let uu____15478
                                                                    =
                                                                    let uu____15479
                                                                    =
                                                                    let uu____15485
                                                                    =
                                                                    let uu____15488
                                                                    =
                                                                    let uu____15490
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15490] in
                                                                    [uu____15488] in
                                                                    let uu____15493
                                                                    =
                                                                    let uu____15494
                                                                    =
                                                                    let uu____15497
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15498
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15497,
                                                                    uu____15498) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15494 in
                                                                    (uu____15485,
                                                                    [x],
                                                                    uu____15493) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15479 in
                                                                    let uu____15508
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15478,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15508) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15474
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15513
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
                                                                    (let uu____15528
                                                                    =
                                                                    let uu____15529
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15529
                                                                    dapp1 in
                                                                    [uu____15528]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15513
                                                                    FStar_List.flatten in
                                                                    let uu____15533
                                                                    =
                                                                    let uu____15537
                                                                    =
                                                                    let uu____15538
                                                                    =
                                                                    let uu____15544
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15550
                                                                    =
                                                                    let uu____15551
                                                                    =
                                                                    let uu____15554
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15554) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15551 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15544,
                                                                    uu____15550) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15538 in
                                                                    (uu____15537,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15533) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____15570 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____15570
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
                                                                 | uu____15596
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15604
                                                                    =
                                                                    let uu____15605
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15605 in
                                                                    if
                                                                    uu____15604
                                                                    then
                                                                    let uu____15612
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15612]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15614
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15627
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15627
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15649
                                                                    =
                                                                    let uu____15653
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15653 in
                                                                    (match uu____15649
                                                                    with
                                                                    | 
                                                                    (uu____15660,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15666
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15666
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15668
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15668
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
                                                             (match uu____15614
                                                              with
                                                              | (uu____15676,arg_vars,elim_eqns_or_guards,uu____15679)
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
                                                                    let uu____15698
                                                                    =
                                                                    let uu____15702
                                                                    =
                                                                    let uu____15703
                                                                    =
                                                                    let uu____15709
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15715
                                                                    =
                                                                    let uu____15716
                                                                    =
                                                                    let uu____15719
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15719) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15716 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15709,
                                                                    uu____15715) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15703 in
                                                                    (uu____15702,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15698 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15732
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15732,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15734
                                                                    =
                                                                    let uu____15738
                                                                    =
                                                                    let uu____15739
                                                                    =
                                                                    let uu____15745
                                                                    =
                                                                    let uu____15748
                                                                    =
                                                                    let uu____15750
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15750] in
                                                                    [uu____15748] in
                                                                    let uu____15753
                                                                    =
                                                                    let uu____15754
                                                                    =
                                                                    let uu____15757
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15758
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15757,
                                                                    uu____15758) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15754 in
                                                                    (uu____15745,
                                                                    [x],
                                                                    uu____15753) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15739 in
                                                                    let uu____15768
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15738,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15768) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15734
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15773
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
                                                                    (let uu____15788
                                                                    =
                                                                    let uu____15789
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15789
                                                                    dapp1 in
                                                                    [uu____15788]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15773
                                                                    FStar_List.flatten in
                                                                    let uu____15793
                                                                    =
                                                                    let uu____15797
                                                                    =
                                                                    let uu____15798
                                                                    =
                                                                    let uu____15804
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15810
                                                                    =
                                                                    let uu____15811
                                                                    =
                                                                    let uu____15814
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15814) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15811 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15804,
                                                                    uu____15810) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15798 in
                                                                    (uu____15797,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15793) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15824 ->
                                                        ((let uu____15826 =
                                                            let uu____15827 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15828 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15827
                                                              uu____15828 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15826);
                                                         ([], []))) in
                                             let uu____15831 = encode_elim () in
                                             (match uu____15831 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15843 =
                                                      let uu____15845 =
                                                        let uu____15847 =
                                                          let uu____15849 =
                                                            let uu____15851 =
                                                              let uu____15852
                                                                =
                                                                let uu____15858
                                                                  =
                                                                  let uu____15860
                                                                    =
                                                                    let uu____15861
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15861 in
                                                                  Some
                                                                    uu____15860 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15858) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15852 in
                                                            [uu____15851] in
                                                          let uu____15864 =
                                                            let uu____15866 =
                                                              let uu____15868
                                                                =
                                                                let uu____15870
                                                                  =
                                                                  let uu____15872
                                                                    =
                                                                    let uu____15874
                                                                    =
                                                                    let uu____15876
                                                                    =
                                                                    let uu____15877
                                                                    =
                                                                    let uu____15881
                                                                    =
                                                                    let uu____15882
                                                                    =
                                                                    let uu____15888
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15888) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15882 in
                                                                    (uu____15881,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15877 in
                                                                    let uu____15895
                                                                    =
                                                                    let uu____15897
                                                                    =
                                                                    let uu____15898
                                                                    =
                                                                    let uu____15902
                                                                    =
                                                                    let uu____15903
                                                                    =
                                                                    let uu____15909
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15915
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15909,
                                                                    uu____15915) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15903 in
                                                                    (uu____15902,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15898 in
                                                                    [uu____15897] in
                                                                    uu____15876
                                                                    ::
                                                                    uu____15895 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15874 in
                                                                  FStar_List.append
                                                                    uu____15872
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15870 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15868 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15866 in
                                                          FStar_List.append
                                                            uu____15849
                                                            uu____15864 in
                                                        FStar_List.append
                                                          decls3 uu____15847 in
                                                      FStar_List.append
                                                        decls2 uu____15845 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15843 in
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
           (fun uu____15936  ->
              fun se  ->
                match uu____15936 with
                | (g,env1) ->
                    let uu____15948 = encode_sigelt env1 se in
                    (match uu____15948 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15984 =
        match uu____15984 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____16002 ->
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
                 ((let uu____16007 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____16007
                   then
                     let uu____16008 = FStar_Syntax_Print.bv_to_string x in
                     let uu____16009 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____16010 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____16008 uu____16009 uu____16010
                   else ());
                  (let uu____16012 = encode_term t1 env1 in
                   match uu____16012 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____16022 =
                         let uu____16026 =
                           let uu____16027 =
                             let uu____16028 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____16028
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____16027 in
                         new_term_constant_from_string env1 x uu____16026 in
                       (match uu____16022 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____16039 = FStar_Options.log_queries () in
                              if uu____16039
                              then
                                let uu____16041 =
                                  let uu____16042 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____16043 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____16044 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____16042 uu____16043 uu____16044 in
                                Some uu____16041
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____16055,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____16064 = encode_free_var env1 fv t t_norm [] in
                 (match uu____16064 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____16077,se,uu____16079) ->
                 let uu____16082 = encode_sigelt env1 se in
                 (match uu____16082 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____16092,se) ->
                 let uu____16096 = encode_sigelt env1 se in
                 (match uu____16096 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____16106 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____16106 with | (uu____16118,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____16163  ->
            match uu____16163 with
            | (l,uu____16170,uu____16171) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____16192  ->
            match uu____16192 with
            | (l,uu____16200,uu____16201) ->
                let uu____16206 =
                  FStar_All.pipe_left
                    (fun _0_49  -> FStar_SMTEncoding_Term.Echo _0_49) (
                    fst l) in
                let uu____16207 =
                  let uu____16209 =
                    let uu____16210 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____16210 in
                  [uu____16209] in
                uu____16206 :: uu____16207)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____16221 =
      let uu____16223 =
        let uu____16224 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____16226 =
          let uu____16227 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____16227 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____16224;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____16226
        } in
      [uu____16223] in
    FStar_ST.write last_env uu____16221
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____16237 = FStar_ST.read last_env in
      match uu____16237 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16243 ->
          let uu___153_16245 = e in
          let uu____16246 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___153_16245.bindings);
            depth = (uu___153_16245.depth);
            tcenv;
            warn = (uu___153_16245.warn);
            cache = (uu___153_16245.cache);
            nolabels = (uu___153_16245.nolabels);
            use_zfuel_name = (uu___153_16245.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_16245.encode_non_total_function_typ);
            current_module_name = uu____16246
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____16250 = FStar_ST.read last_env in
    match uu____16250 with
    | [] -> failwith "Empty env stack"
    | uu____16255::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____16263  ->
    let uu____16264 = FStar_ST.read last_env in
    match uu____16264 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___154_16275 = hd1 in
          {
            bindings = (uu___154_16275.bindings);
            depth = (uu___154_16275.depth);
            tcenv = (uu___154_16275.tcenv);
            warn = (uu___154_16275.warn);
            cache = refs;
            nolabels = (uu___154_16275.nolabels);
            use_zfuel_name = (uu___154_16275.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_16275.encode_non_total_function_typ);
            current_module_name = (uu___154_16275.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____16281  ->
    let uu____16282 = FStar_ST.read last_env in
    match uu____16282 with
    | [] -> failwith "Popping an empty stack"
    | uu____16287::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____16295  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____16298  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____16301  ->
    let uu____16302 = FStar_ST.read last_env in
    match uu____16302 with
    | hd1::uu____16308::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____16314 -> failwith "Impossible"
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
        | (uu____16363::uu____16364,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16368 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16368.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16368.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16368.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16369 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____16380 =
        let uu____16382 =
          let uu____16383 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____16383 in
        let uu____16384 = open_fact_db_tags env in uu____16382 :: uu____16384 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16380
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
      let uu____16399 = encode_sigelt env se in
      match uu____16399 with
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
        let uu____16424 = FStar_Options.log_queries () in
        if uu____16424
        then
          let uu____16426 =
            let uu____16427 =
              let uu____16428 =
                let uu____16429 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____16429 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____16428 in
            FStar_SMTEncoding_Term.Caption uu____16427 in
          uu____16426 :: decls
        else decls in
      let env =
        let uu____16436 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16436 tcenv in
      let uu____16437 = encode_top_level_facts env se in
      match uu____16437 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16446 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____16446))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____16457 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____16457
       then
         let uu____16458 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16458
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16481  ->
                 fun se  ->
                   match uu____16481 with
                   | (g,env2) ->
                       let uu____16493 = encode_top_level_facts env2 se in
                       (match uu____16493 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____16506 =
         encode_signature
           (let uu___156_16510 = env in
            {
              bindings = (uu___156_16510.bindings);
              depth = (uu___156_16510.depth);
              tcenv = (uu___156_16510.tcenv);
              warn = false;
              cache = (uu___156_16510.cache);
              nolabels = (uu___156_16510.nolabels);
              use_zfuel_name = (uu___156_16510.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16510.encode_non_total_function_typ);
              current_module_name = (uu___156_16510.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____16506 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16522 = FStar_Options.log_queries () in
             if uu____16522
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___157_16527 = env1 in
               {
                 bindings = (uu___157_16527.bindings);
                 depth = (uu___157_16527.depth);
                 tcenv = (uu___157_16527.tcenv);
                 warn = true;
                 cache = (uu___157_16527.cache);
                 nolabels = (uu___157_16527.nolabels);
                 use_zfuel_name = (uu___157_16527.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16527.encode_non_total_function_typ);
                 current_module_name = (uu___157_16527.current_module_name)
               });
            (let uu____16529 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____16529
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
        (let uu____16564 =
           let uu____16565 = FStar_TypeChecker_Env.current_module tcenv in
           uu____16565.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16564);
        (let env =
           let uu____16567 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____16567 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____16574 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16595 = aux rest in
                 (match uu____16595 with
                  | (out,rest1) ->
                      let t =
                        let uu____16613 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16613 with
                        | Some uu____16617 ->
                            let uu____16618 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16618
                              x.FStar_Syntax_Syntax.sort
                        | uu____16619 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16622 =
                        let uu____16624 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16625 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16625.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16625.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16624 :: out in
                      (uu____16622, rest1))
             | uu____16628 -> ([], bindings1) in
           let uu____16632 = aux bindings in
           match uu____16632 with
           | (closing,bindings1) ->
               let uu____16646 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16646, bindings1) in
         match uu____16574 with
         | (q1,bindings1) ->
             let uu____16659 =
               let uu____16662 =
                 FStar_List.filter
                   (fun uu___124_16664  ->
                      match uu___124_16664 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16665 ->
                          false
                      | uu____16669 -> true) bindings1 in
               encode_env_bindings env uu____16662 in
             (match uu____16659 with
              | (env_decls,env1) ->
                  ((let uu____16680 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16680
                    then
                      let uu____16681 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16681
                    else ());
                   (let uu____16683 = encode_formula q1 env1 in
                    match uu____16683 with
                    | (phi,qdecls) ->
                        let uu____16695 =
                          let uu____16698 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16698 phi in
                        (match uu____16695 with
                         | (labels,phi1) ->
                             let uu____16708 = encode_labels labels in
                             (match uu____16708 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16729 =
                                      let uu____16733 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16734 =
                                        varops.mk_unique "@query" in
                                      (uu____16733, (Some "query"),
                                        uu____16734) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16729 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16747 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16747 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16749 = encode_formula q env in
       match uu____16749 with
       | (f,uu____16753) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16755) -> true
             | uu____16758 -> false)))