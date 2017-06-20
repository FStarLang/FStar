open Prims
let add_fuel x tl1 =
  let uu____19 = FStar_Options.unthrottle_inductives ()  in
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
            let uu____136 = l1.FStar_Syntax_Syntax.comp ()  in
            FStar_Syntax_Subst.subst_comp s uu____136  in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____133  in
        FStar_Util.Inl uu____132  in
      Some uu____129
  | uu____141 -> l 
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_' 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_158 = a  in
        let uu____159 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____159;
          FStar_Syntax_Syntax.index =
            (uu___126_158.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_158.FStar_Syntax_Syntax.sort)
        }  in
      let uu____160 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____160
  
let primitive_projector_by_pos :
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
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____177  in
        let uu____178 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____178 with
        | (uu____181,t) ->
            let uu____183 =
              let uu____184 = FStar_Syntax_Subst.compress t  in
              uu____184.FStar_Syntax_Syntax.n  in
            (match uu____183 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____199 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____199 with
                  | (binders,uu____203) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid (fst b)))
             | uu____216 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____225 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____225
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____234 =
        let uu____237 = mk_term_projector_name lid a  in
        (uu____237,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____234
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____246 =
        let uu____249 = mk_term_projector_name_by_pos lid i  in
        (uu____249,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____246
  
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x 
type varops_t =
  {
  push: Prims.unit -> Prims.unit ;
  pop: Prims.unit -> Prims.unit ;
  mark: Prims.unit -> Prims.unit ;
  reset_mark: Prims.unit -> Prims.unit ;
  commit_mark: Prims.unit -> Prims.unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: Prims.unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }
let __proj__Mkvarops_t__item__push : varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__push
  
let __proj__Mkvarops_t__item__pop : varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__pop
  
let __proj__Mkvarops_t__item__mark : varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mark
  
let __proj__Mkvarops_t__item__reset_mark :
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__reset_mark
  
let __proj__Mkvarops_t__item__commit_mark :
  varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__commit_mark
  
let __proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_var
  
let __proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_fvar
  
let __proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__fresh
  
let __proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__string_const
  
let __proj__Mkvarops_t__item__next_id : varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__next_id
  
let __proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; mark = __fname__mark;
        reset_mark = __fname__reset_mark; commit_mark = __fname__commit_mark;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mk_unique
  
let varops : varops_t =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____863 =
    let uu____864 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____866 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____864, uu____866)  in
  let scopes =
    let uu____877 = let uu____883 = new_scope ()  in [uu____883]  in
    FStar_Util.mk_ref uu____877  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____908 =
        let uu____910 = FStar_ST.read scopes  in
        FStar_Util.find_map uu____910
          (fun uu____927  ->
             match uu____927 with
             | (names1,uu____934) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____908 with
      | None  -> y1
      | Some uu____939 ->
          (FStar_Util.incr ctr;
           (let uu____944 =
              let uu____945 =
                let uu____946 = FStar_ST.read ctr  in
                Prims.string_of_int uu____946  in
              Prims.strcat "__" uu____945  in
            Prims.strcat y1 uu____944))
       in
    let top_scope =
      let uu____951 =
        let uu____956 = FStar_ST.read scopes  in FStar_List.hd uu____956  in
      FStar_All.pipe_left FStar_Pervasives.fst uu____951  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____995 = FStar_Util.incr ctr; FStar_ST.read ctr  in
  let fresh1 pfx =
    let uu____1006 =
      let uu____1007 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1007  in
    FStar_Util.format2 "%s_%s" pfx uu____1006  in
  let string_const s =
    let uu____1012 =
      let uu____1014 = FStar_ST.read scopes  in
      FStar_Util.find_map uu____1014
        (fun uu____1031  ->
           match uu____1031 with
           | (uu____1037,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1012 with
    | Some f -> f
    | None  ->
        let id = next_id1 ()  in
        let f =
          let uu____1046 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1046  in
        let top_scope =
          let uu____1049 =
            let uu____1054 = FStar_ST.read scopes  in
            FStar_List.hd uu____1054  in
          FStar_All.pipe_left FStar_Pervasives.snd uu____1049  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1082 =
    let uu____1083 =
      let uu____1089 = new_scope ()  in
      let uu____1094 = FStar_ST.read scopes  in uu____1089 :: uu____1094  in
    FStar_ST.write scopes uu____1083  in
  let pop1 uu____1121 =
    let uu____1122 =
      let uu____1128 = FStar_ST.read scopes  in FStar_List.tl uu____1128  in
    FStar_ST.write scopes uu____1122  in
  let mark1 uu____1155 = push1 ()  in
  let reset_mark1 uu____1159 = pop1 ()  in
  let commit_mark1 uu____1163 =
    let uu____1164 = FStar_ST.read scopes  in
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
    | uu____1224 -> failwith "Impossible"  in
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
let unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___127_1234 = x  in
    let uu____1235 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1235;
      FStar_Syntax_Syntax.index = (uu___127_1234.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_1234.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) 
  | Binding_fvar of (FStar_Ident.lident * Prims.string *
  FStar_SMTEncoding_Term.term option * FStar_SMTEncoding_Term.term option) 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1259 -> false
  
let __proj__Binding_var__item___0 :
  binding -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1285 -> false
  
let __proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident * Prims.string * FStar_SMTEncoding_Term.term option *
      FStar_SMTEncoding_Term.term option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar v1 = (v1, None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }
let __proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let __proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let __proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let __proj__Mkcache_entry__item__cache_symbol_assumption_names :
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
  bindings: binding Prims.list ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string }
let __proj__Mkenv_t__item__bindings : env_t -> binding Prims.list =
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
  
let __proj__Mkenv_t__item__depth : env_t -> Prims.int =
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
  
let __proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env =
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
  
let __proj__Mkenv_t__item__warn : env_t -> Prims.bool =
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
  
let __proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap =
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
  
let __proj__Mkenv_t__item__nolabels : env_t -> Prims.bool =
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
  
let __proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool =
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
  
let __proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool =
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
  
let __proj__Mkenv_t__item__current_module_name : env_t -> Prims.string =
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
         (fun uu___103_1609  ->
            match uu___103_1609 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1612 -> []))
     in
  {
    cache_symbol_name = tsym;
    cache_symbol_arg_sorts = cvar_sorts;
    cache_symbol_decls = t_decls;
    cache_symbol_assumption_names = names1
  } 
let use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let print_env : env_t -> Prims.string =
  fun e  ->
    let uu____1622 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___104_1626  ->
              match uu___104_1626 with
              | Binding_var (x,uu____1628) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1630,uu____1631,uu____1632) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____1622 (FStar_String.concat ", ")
  
let lookup_binding env f = FStar_Util.find_map env.bindings f 
let caption_t : env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
  fun env  ->
    fun t  ->
      let uu____1670 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____1670
      then
        let uu____1672 = FStar_Syntax_Print.term_to_string t  in
        Some uu____1672
      else None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____1685 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____1685)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___128_1699 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1699.tcenv);
           warn = (uu___128_1699.warn);
           cache = (uu___128_1699.cache);
           nolabels = (uu___128_1699.nolabels);
           use_zfuel_name = (uu___128_1699.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1699.encode_non_total_function_typ);
           current_module_name = (uu___128_1699.current_module_name)
         }))
  
let new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      (ysym, y,
        (let uu___129_1714 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1714.depth);
           tcenv = (uu___129_1714.tcenv);
           warn = (uu___129_1714.warn);
           cache = (uu___129_1714.cache);
           nolabels = (uu___129_1714.nolabels);
           use_zfuel_name = (uu___129_1714.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1714.encode_non_total_function_typ);
           current_module_name = (uu___129_1714.current_module_name)
         }))
  
let new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string * FStar_SMTEncoding_Term.term * env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        (ysym, y,
          (let uu___130_1733 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1733.depth);
             tcenv = (uu___130_1733.tcenv);
             warn = (uu___130_1733.warn);
             cache = (uu___130_1733.cache);
             nolabels = (uu___130_1733.nolabels);
             use_zfuel_name = (uu___130_1733.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1733.encode_non_total_function_typ);
             current_module_name = (uu___130_1733.current_module_name)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1746 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1746.depth);
          tcenv = (uu___131_1746.tcenv);
          warn = (uu___131_1746.warn);
          cache = (uu___131_1746.cache);
          nolabels = (uu___131_1746.nolabels);
          use_zfuel_name = (uu___131_1746.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1746.encode_non_total_function_typ);
          current_module_name = (uu___131_1746.current_module_name)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_1764  ->
             match uu___105_1764 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1772 -> None)
         in
      let uu____1775 = aux a  in
      match uu____1775 with
      | None  ->
          let a2 = unmangle a  in
          let uu____1782 = aux a2  in
          (match uu____1782 with
           | None  ->
               let uu____1788 =
                 let uu____1789 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____1790 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1789 uu____1790
                  in
               failwith uu____1788
           | Some (b,t) -> t)
      | Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t -> FStar_Ident.lident -> (Prims.string * Prims.string * env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____1812 =
        let uu___132_1813 = env  in
        let uu____1814 =
          let uu____1816 =
            let uu____1817 =
              let uu____1824 =
                let uu____1826 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left (fun _0_39  -> Some _0_39) uu____1826  in
              (x, fname, uu____1824, None)  in
            Binding_fvar uu____1817  in
          uu____1816 :: (env.bindings)  in
        {
          bindings = uu____1814;
          depth = (uu___132_1813.depth);
          tcenv = (uu___132_1813.tcenv);
          warn = (uu___132_1813.warn);
          cache = (uu___132_1813.cache);
          nolabels = (uu___132_1813.nolabels);
          use_zfuel_name = (uu___132_1813.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1813.encode_non_total_function_typ);
          current_module_name = (uu___132_1813.current_module_name)
        }  in
      (fname, ftok, uu____1812)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term option *
        FStar_SMTEncoding_Term.term option) option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___106_1850  ->
           match uu___106_1850 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1872 -> None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1886 =
        lookup_binding env
          (fun uu___107_1888  ->
             match uu___107_1888 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1898 -> None)
         in
      FStar_All.pipe_right uu____1886 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string * FStar_SMTEncoding_Term.term option *
        FStar_SMTEncoding_Term.term option)
  =
  fun env  ->
    fun a  ->
      let uu____1913 = try_lookup_lid env a  in
      match uu____1913 with
      | None  ->
          let uu____1930 =
            let uu____1931 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____1931  in
          failwith uu____1930
      | Some s -> s
  
let push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___133_1966 = env  in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___133_1966.depth);
            tcenv = (uu___133_1966.tcenv);
            warn = (uu___133_1966.warn);
            cache = (uu___133_1966.cache);
            nolabels = (uu___133_1966.nolabels);
            use_zfuel_name = (uu___133_1966.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1966.encode_non_total_function_typ);
            current_module_name = (uu___133_1966.current_module_name)
          }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1981 = lookup_lid env x  in
        match uu____1981 with
        | (t1,t2,uu____1989) ->
            let t3 =
              let uu____1995 =
                let uu____1999 =
                  let uu____2001 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____2001]  in
                (f, uu____1999)  in
              FStar_SMTEncoding_Util.mkApp uu____1995  in
            let uu___134_2004 = env  in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___134_2004.depth);
              tcenv = (uu___134_2004.tcenv);
              warn = (uu___134_2004.warn);
              cache = (uu___134_2004.cache);
              nolabels = (uu___134_2004.nolabels);
              use_zfuel_name = (uu___134_2004.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_2004.encode_non_total_function_typ);
              current_module_name = (uu___134_2004.current_module_name)
            }
  
let try_lookup_free_var :
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
  fun env  ->
    fun l  ->
      let uu____2016 = try_lookup_lid env l  in
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
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2053
                               FStar_Pervasives.fst
                              in
                           FStar_Util.starts_with uu____2052 "fuel"  in
                         if uu____2051
                         then
                           let uu____2055 =
                             let uu____2056 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2056
                               fuel
                              in
                           FStar_All.pipe_left (fun _0_40  -> Some _0_40)
                             uu____2055
                         else Some t
                     | uu____2059 -> Some t)
                | uu____2060 -> None))
  
let lookup_free_var env a =
  let uu____2081 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
  match uu____2081 with
  | Some t -> t
  | None  ->
      let uu____2084 =
        let uu____2085 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
        FStar_Util.format1 "Name not found: %s" uu____2085  in
      failwith uu____2084
  
let lookup_free_var_name env a =
  let uu____2105 = lookup_lid env a.FStar_Syntax_Syntax.v  in
  match uu____2105 with | (x,uu____2112,uu____2113) -> x 
let lookup_free_var_sym env a =
  let uu____2140 = lookup_lid env a.FStar_Syntax_Syntax.v  in
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
  
let tok_of_name : env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___108_2195  ->
           match uu___108_2195 with
           | Binding_fvar (uu____2197,nm',tok,uu____2200) when nm = nm' ->
               tok
           | uu____2205 -> None)
  
let mkForall_fuel' n1 uu____2225 =
  match uu____2225 with
  | (pats,vars,body) ->
      let fallback uu____2241 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
      let uu____2244 = FStar_Options.unthrottle_inductives ()  in
      if uu____2244
      then fallback ()
      else
        (let uu____2246 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
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
                       | uu____2265 -> p))
                in
             let pats1 = FStar_List.map add_fuel1 pats  in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____2279 = add_fuel1 guards  in
                         FStar_SMTEncoding_Util.mk_and_l uu____2279
                     | uu____2281 ->
                         let uu____2282 = add_fuel1 [guard]  in
                         FStar_All.pipe_right uu____2282 FStar_List.hd
                      in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____2285 -> body  in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars  in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list *
    FStar_SMTEncoding_Term.fvs * FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1") 
let head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____2314 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____2322 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____2327 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____2328 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____2337 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____2347 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2349 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2349 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____2363;
             FStar_Syntax_Syntax.pos = uu____2364;
             FStar_Syntax_Syntax.vars = uu____2365;_},uu____2366)
          ->
          let uu____2381 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2381 FStar_Option.isNone
      | uu____2394 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____2403 =
        let uu____2404 = FStar_Syntax_Util.un_uinst t  in
        uu____2404.FStar_Syntax_Syntax.n  in
      match uu____2403 with
      | FStar_Syntax_Syntax.Tm_abs (uu____2407,uu____2408,Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Syntax_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___109_2421  ->
                  match uu___109_2421 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____2422 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____2424 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____2424 FStar_Option.isSome
      | uu____2437 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____2446 = head_normal env t  in
      if uu____2446
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let norm : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____2460 =
      let uu____2461 = FStar_Syntax_Syntax.null_binder t  in [uu____2461]  in
    let uu____2462 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None
       in
    FStar_Syntax_Util.abs uu____2460 uu____2462 None
  
let mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
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
                    let uu____2486 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____2486
                | s ->
                    let uu____2489 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____2489) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___110_2504  ->
    match uu___110_2504 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____2505 -> false
  
let is_an_eta_expansion :
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
                       FStar_SMTEncoding_Term.freevars = uu____2536;
                       FStar_SMTEncoding_Term.rng = uu____2537;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2551) ->
              let uu____2556 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2570 -> false) args (FStar_List.rev xs))
                 in
              if uu____2556 then tok_of_name env f else None
          | (uu____2573,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____2576 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2578 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____2578))
                 in
              if uu____2576 then Some t else None
          | uu____2581 -> None  in
        check_partial_applications body (FStar_List.rev vars)
  
type label = (FStar_SMTEncoding_Term.fv * Prims.string * FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list
    }
let __proj__Mkpattern__item__pat_vars :
  pattern -> (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.fv) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let __proj__Mkpattern__item__pat_term :
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let __proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let __proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
exception Let_rec_unencodeable 
let uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____2748 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___111_2752  ->
    match uu___111_2752 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2754 =
          let uu____2758 =
            let uu____2760 =
              let uu____2761 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)
                 in
              FStar_SMTEncoding_Term.boxInt uu____2761  in
            [uu____2760]  in
          ("FStar.Char.Char", uu____2758)  in
        FStar_SMTEncoding_Util.mkApp uu____2754
    | FStar_Const.Const_int (i,None ) ->
        let uu____2769 = FStar_SMTEncoding_Util.mkInteger i  in
        FStar_SMTEncoding_Term.boxInt uu____2769
    | FStar_Const.Const_int (i,Some uu____2771) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2780) ->
        let uu____2783 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes
           in
        varops.string_const uu____2783
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2787 =
          let uu____2788 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "Unhandled constant: %s" uu____2788  in
        failwith uu____2787
  
let as_function_typ :
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____2809 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2817 ->
            let uu____2822 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____2822
        | uu____2823 ->
            if norm1
            then let uu____2824 = whnf env t1  in aux false uu____2824
            else
              (let uu____2826 =
                 let uu____2827 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____2828 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2827 uu____2828
                  in
               failwith uu____2826)
         in
      aux true t0
  
let curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders * FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2850 ->
        let uu____2851 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____2851)
  
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2883::uu____2884::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2887::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2889 -> false 
let rec encode_binders :
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list * FStar_SMTEncoding_Term.term
          Prims.list * env_t * FStar_SMTEncoding_Term.decls_t *
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____3027 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____3027
         then
           let uu____3028 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____3028
         else ());
        (let uu____3030 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____3066  ->
                   fun b  ->
                     match uu____3066 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____3109 =
                           let x = unmangle (fst b)  in
                           let uu____3118 = gen_term_var env1 x  in
                           match uu____3118 with
                           | (xxsym,xx,env') ->
                               let uu____3132 =
                                 let uu____3135 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____3135 env1 xx
                                  in
                               (match uu____3132 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____3109 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____3030 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and encode_term_pred :
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____3223 = encode_term t env  in
          match uu____3223 with
          | (t1,decls) ->
              let uu____3230 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____3230, decls)

and encode_term_pred' :
  FStar_SMTEncoding_Term.term option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____3238 = encode_term t env  in
          match uu____3238 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____3247 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____3247, decls)
               | Some f ->
                   let uu____3249 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____3249, decls))

and encode_arith_term :
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____3255 = encode_args args_e env  in
        match uu____3255 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____3267 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____3274 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____3274  in
            let binary arg_tms1 =
              let uu____3283 =
                let uu____3284 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____3284  in
              let uu____3285 =
                let uu____3286 =
                  let uu____3287 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____3287  in
                FStar_SMTEncoding_Term.unboxInt uu____3286  in
              (uu____3283, uu____3285)  in
            let mk_default uu____3292 =
              let uu____3293 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____3293 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms))
               in
            let mk_l op mk_args ts =
              let uu____3338 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____3338
              then
                let uu____3339 =
                  let uu____3340 = mk_args ts  in op uu____3340  in
                FStar_All.pipe_right uu____3339 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____3363 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____3363
              then
                let uu____3364 = binary ts  in
                match uu____3364 with
                | (t1,t2) ->
                    let uu____3369 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____3369
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____3372 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____3372
                 then
                   let uu____3373 = op (binary ts)  in
                   FStar_All.pipe_right uu____3373
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary  in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary  in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary  in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Syntax_Const.op_Addition, add1);
              (FStar_Syntax_Const.op_Subtraction, sub1);
              (FStar_Syntax_Const.op_Multiply, mul1);
              (FStar_Syntax_Const.op_Division, div1);
              (FStar_Syntax_Const.op_Modulus, modulus);
              (FStar_Syntax_Const.op_Minus, minus)]  in
            let uu____3463 =
              let uu____3469 =
                FStar_List.tryFind
                  (fun uu____3481  ->
                     match uu____3481 with
                     | (l,uu____3488) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____3469 FStar_Util.must  in
            (match uu____3463 with
             | (uu____3513,op) ->
                 let uu____3521 = op arg_tms  in (uu____3521, decls))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____3528 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____3528
       then
         let uu____3529 = FStar_Syntax_Print.tag_of_term t  in
         let uu____3530 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____3531 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____3529 uu____3530
           uu____3531
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____3535 ->
           let uu____3550 =
             let uu____3551 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3552 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3553 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3554 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3551
               uu____3552 uu____3553 uu____3554
              in
           failwith uu____3550
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____3557 =
             let uu____3558 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____3559 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____3560 = FStar_Syntax_Print.term_to_string t0  in
             let uu____3561 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____3558
               uu____3559 uu____3560 uu____3561
              in
           failwith uu____3557
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____3565 =
             let uu____3566 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____3566
              in
           failwith uu____3565
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____3571) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____3601) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____3610 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____3610, [])
       | FStar_Syntax_Syntax.Tm_type uu____3616 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____3619) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____3625 = encode_const c  in (uu____3625, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____3640 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____3640 with
            | (binders1,res) ->
                let uu____3647 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____3647
                then
                  let uu____3650 = encode_binders None binders1 env  in
                  (match uu____3650 with
                   | (vars,guards,env',decls,uu____3665) ->
                       let fsym =
                         let uu____3675 = varops.fresh "f"  in
                         (uu____3675, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____3678 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_3682 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_3682.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_3682.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_3682.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_3682.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_3682.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_3682.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_3682.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_3682.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_3682.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_3682.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_3682.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_3682.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_3682.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_3682.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_3682.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_3682.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_3682.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_3682.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_3682.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_3682.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_3682.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_3682.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_3682.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___135_3682.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___135_3682.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___135_3682.FStar_TypeChecker_Env.is_native_tactic)
                            }) res
                          in
                       (match uu____3678 with
                        | (pre_opt,res_t) ->
                            let uu____3689 =
                              encode_term_pred None res_t env' app  in
                            (match uu____3689 with
                             | (res_pred,decls') ->
                                 let uu____3696 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____3703 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____3703, [])
                                   | Some pre ->
                                       let uu____3706 =
                                         encode_formula pre env'  in
                                       (match uu____3706 with
                                        | (guard,decls0) ->
                                            let uu____3714 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____3714, decls0))
                                    in
                                 (match uu____3696 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3722 =
                                          let uu____3728 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____3728)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3722
                                         in
                                      let cvars =
                                        let uu____3738 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____3738
                                          (FStar_List.filter
                                             (fun uu____3744  ->
                                                match uu____3744 with
                                                | (x,uu____3748) ->
                                                    x <> (fst fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____3759 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____3759 with
                                       | Some cache_entry ->
                                           let uu____3764 =
                                             let uu____3765 =
                                               let uu____3769 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3769)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3765
                                              in
                                           (uu____3764,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3780 =
                                               let uu____3781 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3781
                                                in
                                             varops.mk_unique uu____3780  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars
                                              in
                                           let caption =
                                             let uu____3788 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____3788
                                             then
                                               let uu____3790 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               Some uu____3790
                                             else None  in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____3796 =
                                               let uu____3800 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____3800)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3796
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____3808 =
                                               let uu____3812 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____3812, (Some a_name),
                                                 a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3808
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____3825 =
                                               let uu____3829 =
                                                 let uu____3830 =
                                                   let uu____3836 =
                                                     let uu____3837 =
                                                       let uu____3840 =
                                                         let uu____3841 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3841
                                                          in
                                                       (f_has_t, uu____3840)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3837
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3836)
                                                    in
                                                 mkForall_fuel uu____3830  in
                                               (uu____3829,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3825
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____3854 =
                                               let uu____3858 =
                                                 let uu____3859 =
                                                   let uu____3865 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3865)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3859
                                                  in
                                               (uu____3858, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3854
                                              in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____3879 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3879);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____3890 =
                       let uu____3894 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____3894, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3890  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____3903 =
                       let uu____3907 =
                         let uu____3908 =
                           let uu____3914 =
                             let uu____3915 =
                               let uu____3918 =
                                 let uu____3919 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3919
                                  in
                               (f_has_t, uu____3918)  in
                             FStar_SMTEncoding_Util.mkImp uu____3915  in
                           ([[f_has_t]], [fsym], uu____3914)  in
                         mkForall_fuel uu____3908  in
                       (uu____3907, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____3903  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3933 ->
           let uu____3938 =
             let uu____3941 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____3941 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3946;
                 FStar_Syntax_Syntax.pos = uu____3947;
                 FStar_Syntax_Syntax.vars = uu____3948;_} ->
                 let uu____3955 = FStar_Syntax_Subst.open_term [(x, None)] f
                    in
                 (match uu____3955 with
                  | (b,f1) ->
                      let uu____3969 =
                        let uu____3970 = FStar_List.hd b  in fst uu____3970
                         in
                      (uu____3969, f1))
             | uu____3975 -> failwith "impossible"  in
           (match uu____3938 with
            | (x,f) ->
                let uu____3982 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____3982 with
                 | (base_t,decls) ->
                     let uu____3989 = gen_term_var env x  in
                     (match uu____3989 with
                      | (x1,xtm,env') ->
                          let uu____3998 = encode_formula f env'  in
                          (match uu____3998 with
                           | (refinement,decls') ->
                               let uu____4005 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____4005 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____4016 =
                                        let uu____4018 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____4022 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____4018
                                          uu____4022
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____4016
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____4038  ->
                                              match uu____4038 with
                                              | (y,uu____4042) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____4061 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____4061 with
                                     | Some cache_entry ->
                                         let uu____4066 =
                                           let uu____4067 =
                                             let uu____4071 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____4071)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4067
                                            in
                                         (uu____4066,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____4083 =
                                             let uu____4084 =
                                               let uu____4085 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____4085
                                                in
                                             Prims.strcat module_name
                                               uu____4084
                                              in
                                           varops.mk_unique uu____4083  in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None)
                                            in
                                         let t1 =
                                           let uu____4094 =
                                             let uu____4098 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____4098)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____4094
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____4109 =
                                             let uu____4113 =
                                               let uu____4114 =
                                                 let uu____4120 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____4120)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4114
                                                in
                                             (uu____4113,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4109
                                            in
                                         let t_valid =
                                           let xx =
                                             (x1,
                                               FStar_SMTEncoding_Term.Term_sort)
                                              in
                                           let valid_t =
                                             FStar_SMTEncoding_Util.mkApp
                                               ("Valid", [t1])
                                              in
                                           let uu____4135 =
                                             let uu____4139 =
                                               let uu____4140 =
                                                 let uu____4146 =
                                                   let uu____4147 =
                                                     let uu____4150 =
                                                       let uu____4151 =
                                                         let uu____4157 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement)
                                                            in
                                                         ([], [xx],
                                                           uu____4157)
                                                          in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____4151
                                                        in
                                                     (uu____4150, valid_t)
                                                      in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____4147
                                                    in
                                                 ([[valid_t]], cvars1,
                                                   uu____4146)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4140
                                                in
                                             (uu____4139,
                                               (Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4135
                                            in
                                         let t_kinding =
                                           let uu____4177 =
                                             let uu____4181 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____4181,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4177
                                            in
                                         let t_interp =
                                           let uu____4191 =
                                             let uu____4195 =
                                               let uu____4196 =
                                                 let uu____4202 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____4202)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____4196
                                                in
                                             let uu____4214 =
                                               let uu____4216 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               Some uu____4216  in
                                             (uu____4195, uu____4214,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____4191
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_valid;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____4221 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____4221);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____4238 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____4238  in
           let uu____4239 = encode_term_pred None k env ttm  in
           (match uu____4239 with
            | (t_has_k,decls) ->
                let d =
                  let uu____4247 =
                    let uu____4251 =
                      let uu____4252 =
                        let uu____4253 =
                          let uu____4254 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____4254
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____4253  in
                      varops.mk_unique uu____4252  in
                    (t_has_k, (Some "Uvar typing"), uu____4251)  in
                  FStar_SMTEncoding_Util.mkAssume uu____4247  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____4257 ->
           let uu____4267 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____4267 with
            | (head1,args_e) ->
                let uu____4295 =
                  let uu____4303 =
                    let uu____4304 = FStar_Syntax_Subst.compress head1  in
                    uu____4304.FStar_Syntax_Syntax.n  in
                  (uu____4303, args_e)  in
                (match uu____4295 with
                 | uu____4314 when head_redex env head1 ->
                     let uu____4322 = whnf env t  in
                     encode_term uu____4322 env
                 | uu____4323 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____4336;
                       FStar_Syntax_Syntax.pos = uu____4337;
                       FStar_Syntax_Syntax.vars = uu____4338;_},uu____4339),uu____4340::
                    (v1,uu____4342)::(v2,uu____4344)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4382 = encode_term v1 env  in
                     (match uu____4382 with
                      | (v11,decls1) ->
                          let uu____4389 = encode_term v2 env  in
                          (match uu____4389 with
                           | (v21,decls2) ->
                               let uu____4396 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____4396,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____4399::(v1,uu____4401)::(v2,uu____4403)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____4437 = encode_term v1 env  in
                     (match uu____4437 with
                      | (v11,decls1) ->
                          let uu____4444 = encode_term v2 env  in
                          (match uu____4444 with
                           | (v21,decls2) ->
                               let uu____4451 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____4451,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____4453) ->
                     let e0 =
                       let uu____4465 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____4465
                        in
                     ((let uu____4471 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____4471
                       then
                         let uu____4472 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____4472
                       else ());
                      (let e =
                         let uu____4477 =
                           let uu____4478 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____4479 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____4478
                             uu____4479
                            in
                         uu____4477 None t0.FStar_Syntax_Syntax.pos  in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____4488),(arg,uu____4490)::[]) -> encode_term arg env
                 | uu____4508 ->
                     let uu____4516 = encode_args args_e env  in
                     (match uu____4516 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____4549 = encode_term head1 env  in
                            match uu____4549 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____4588 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____4588 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____4632  ->
                                                 fun uu____4633  ->
                                                   match (uu____4632,
                                                           uu____4633)
                                                   with
                                                   | ((bv,uu____4647),
                                                      (a,uu____4649)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____4663 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____4663
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____4668 =
                                            encode_term_pred None ty env
                                              app_tm
                                             in
                                          (match uu____4668 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____4678 =
                                                   let uu____4682 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____4687 =
                                                     let uu____4688 =
                                                       let uu____4689 =
                                                         let uu____4690 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____4690
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____4689
                                                        in
                                                     varops.mk_unique
                                                       uu____4688
                                                      in
                                                   (uu____4682,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____4687)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____4678
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____4707 = lookup_free_var_sym env fv  in
                            match uu____4707 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args))
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.tk = uu____4730;
                                   FStar_Syntax_Syntax.pos = uu____4731;
                                   FStar_Syntax_Syntax.vars = uu____4732;_},uu____4733)
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.tk = uu____4744;
                                   FStar_Syntax_Syntax.pos = uu____4745;
                                   FStar_Syntax_Syntax.vars = uu____4746;_},uu____4747)
                                ->
                                let uu____4752 =
                                  let uu____4753 =
                                    let uu____4756 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____4756
                                      FStar_Pervasives.fst
                                     in
                                  FStar_All.pipe_right uu____4753
                                    FStar_Pervasives.snd
                                   in
                                Some uu____4752
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4776 =
                                  let uu____4777 =
                                    let uu____4780 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____4780
                                      FStar_Pervasives.fst
                                     in
                                  FStar_All.pipe_right uu____4777
                                    FStar_Pervasives.snd
                                   in
                                Some uu____4776
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4799,(FStar_Util.Inl t1,uu____4801),uu____4802)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4840,(FStar_Util.Inr c,uu____4842),uu____4843)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4881 -> None  in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4901 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4901
                                  in
                               let uu____4902 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____4902 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4912;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4913;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4914;_},uu____4915)
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
                                     | uu____4947 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4987 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____4987 with
            | (bs1,body1,opening) ->
                let fallback uu____5002 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding"))
                     in
                  let uu____5007 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____5007, [decl])  in
                let is_impure rc =
                  let uu____5013 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____5013 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | None  ->
                        let uu____5022 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____5022 FStar_Pervasives.fst
                    | Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Syntax_Const.effect_Tot_lid
                  then
                    let uu____5035 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    Some uu____5035
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Syntax_Const.effect_GTot_lid
                    then
                      (let uu____5038 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       Some uu____5038)
                    else None
                   in
                (match lopt with
                 | None  ->
                     ((let uu____5043 =
                         let uu____5044 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____5044
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____5043);
                      fallback ())
                 | Some rc ->
                     let uu____5046 =
                       (is_impure rc) &&
                         (let uu____5047 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____5047)
                        in
                     if uu____5046
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____5052 = encode_binders None bs1 env  in
                        match uu____5052 with
                        | (vars,guards,envbody,decls,uu____5067) ->
                            let body2 =
                              FStar_TypeChecker_Util.reify_body env.tcenv
                                body1
                               in
                            let uu____5075 = encode_term body2 envbody  in
                            (match uu____5075 with
                             | (body3,decls') ->
                                 let uu____5082 =
                                   let uu____5087 = codomain_eff rc  in
                                   match uu____5087 with
                                   | None  -> (None, [])
                                   | Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____5099 = encode_term tfun env
                                          in
                                       (match uu____5099 with
                                        | (t1,decls1) -> ((Some t1), decls1))
                                    in
                                 (match uu____5082 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____5118 =
                                          let uu____5124 =
                                            let uu____5125 =
                                              let uu____5128 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____5128, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____5125
                                             in
                                          ([], vars, uu____5124)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____5118
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | None  -> cvars
                                        | Some t1 ->
                                            let uu____5136 =
                                              let uu____5138 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____5138
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____5136
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____5149 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____5149 with
                                       | Some cache_entry ->
                                           let uu____5154 =
                                             let uu____5155 =
                                               let uu____5159 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____5159)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____5155
                                              in
                                           (uu____5154,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let uu____5165 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____5165 with
                                            | Some t1 ->
                                                let decls1 =
                                                  let uu____5172 =
                                                    let uu____5173 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____5173 = cache_size
                                                     in
                                                  if uu____5172
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | None  ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____5184 =
                                                      let uu____5185 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____5185
                                                       in
                                                    varops.mk_unique
                                                      uu____5184
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      None)
                                                   in
                                                let f =
                                                  let uu____5190 =
                                                    let uu____5194 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____5194)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____5190
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | None  -> []
                                                  | Some t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          None f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____5206 =
                                                        let uu____5207 =
                                                          let uu____5211 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____5211,
                                                            (Some a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____5207
                                                         in
                                                      [uu____5206]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____5219 =
                                                    let uu____5223 =
                                                      let uu____5224 =
                                                        let uu____5230 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____5230)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____5224
                                                       in
                                                    (uu____5223,
                                                      (Some a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____5219
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____5240 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____5240);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____5242,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____5243;
                          FStar_Syntax_Syntax.lbunivs = uu____5244;
                          FStar_Syntax_Syntax.lbtyp = uu____5245;
                          FStar_Syntax_Syntax.lbeff = uu____5246;
                          FStar_Syntax_Syntax.lbdef = uu____5247;_}::uu____5248),uu____5249)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____5267;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____5269;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____5285 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None)
                in
             let uu____5298 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____5298, [decl_e])))
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term *
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____5340 = encode_term e1 env  in
              match uu____5340 with
              | (ee1,decls1) ->
                  let uu____5347 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2  in
                  (match uu____5347 with
                   | (xs,e21) ->
                       let uu____5361 = FStar_List.hd xs  in
                       (match uu____5361 with
                        | (x1,uu____5369) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____5371 = encode_body e21 env'  in
                            (match uu____5371 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____5393 =
              let uu____5397 =
                let uu____5398 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____5398  in
              gen_term_var env uu____5397  in
            match uu____5393 with
            | (scrsym,scr',env1) ->
                let uu____5408 = encode_term e env1  in
                (match uu____5408 with
                 | (scr,decls) ->
                     let uu____5415 =
                       let encode_branch b uu____5431 =
                         match uu____5431 with
                         | (else_case,decls1) ->
                             let uu____5442 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____5442 with
                              | (p,w,br) ->
                                  let uu____5463 = encode_pat env1 p  in
                                  (match uu____5463 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____5483  ->
                                                   match uu____5483 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____5488 =
                                         match w with
                                         | None  -> (guard, [])
                                         | Some w1 ->
                                             let uu____5503 =
                                               encode_term w1 env2  in
                                             (match uu____5503 with
                                              | (w2,decls2) ->
                                                  let uu____5511 =
                                                    let uu____5512 =
                                                      let uu____5515 =
                                                        let uu____5516 =
                                                          let uu____5519 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____5519)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____5516
                                                         in
                                                      (guard, uu____5515)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____5512
                                                     in
                                                  (uu____5511, decls2))
                                          in
                                       (match uu____5488 with
                                        | (guard1,decls2) ->
                                            let uu____5527 =
                                              encode_br br env2  in
                                            (match uu____5527 with
                                             | (br1,decls3) ->
                                                 let uu____5535 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____5535,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____5415 with
                      | (match_tm,decls1) ->
                          let uu____5546 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____5546, decls1)))

and encode_pat : env_t -> FStar_Syntax_Syntax.pat -> (env_t * pattern) =
  fun env  ->
    fun pat  ->
      (let uu____5568 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____5568
       then
         let uu____5569 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____5569
       else ());
      (let uu____5571 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____5571 with
       | (vars,pat_term) ->
           let uu____5581 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____5604  ->
                     fun v1  ->
                       match uu____5604 with
                       | (env1,vars1) ->
                           let uu____5632 = gen_term_var env1 v1  in
                           (match uu____5632 with
                            | (xx,uu____5644,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____5581 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5691 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5692 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5693 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5699 =
                        let uu____5702 = encode_const c  in
                        (scrutinee, uu____5702)  in
                      FStar_SMTEncoding_Util.mkEq uu____5699
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____5721 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____5721 with
                        | (uu____5725,uu____5726::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5728 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5749  ->
                                  match uu____5749 with
                                  | (arg,uu____5755) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____5765 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____5765))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5785) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5804 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5819 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5841  ->
                                  match uu____5841 with
                                  | (arg,uu____5850) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____5860 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____5860))
                         in
                      FStar_All.pipe_right uu____5819 FStar_List.flatten
                   in
                let pat_term1 uu____5876 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list *
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____5883 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5898  ->
                fun uu____5899  ->
                  match (uu____5898, uu____5899) with
                  | ((tms,decls),(t,uu____5919)) ->
                      let uu____5930 = encode_term t env  in
                      (match uu____5930 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____5883 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5964 = FStar_Syntax_Util.list_elements e  in
        match uu____5964 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             [])
         in
      let one_pat p =
        let uu____5979 =
          let uu____5989 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____5989 FStar_Syntax_Util.head_and_args  in
        match uu____5979 with
        | (head1,args) ->
            let uu____6017 =
              let uu____6025 =
                let uu____6026 = FStar_Syntax_Util.un_uinst head1  in
                uu____6026.FStar_Syntax_Syntax.n  in
              (uu____6025, args)  in
            (match uu____6017 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____6037,uu____6038)::(e,uu____6040)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> e
             | uu____6066 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____6093 =
            let uu____6103 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____6103 FStar_Syntax_Util.head_and_args
             in
          match uu____6093 with
          | (head1,args) ->
              let uu____6132 =
                let uu____6140 =
                  let uu____6141 = FStar_Syntax_Util.un_uinst head1  in
                  uu____6141.FStar_Syntax_Syntax.n  in
                (uu____6140, args)  in
              (match uu____6132 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____6154)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____6174 -> None)
           in
        match elts with
        | t1::[] ->
            let uu____6189 = smt_pat_or1 t1  in
            (match uu____6189 with
             | Some e ->
                 let uu____6202 = list_elements1 e  in
                 FStar_All.pipe_right uu____6202
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____6213 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____6213
                           (FStar_List.map one_pat)))
             | uu____6221 ->
                 let uu____6225 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____6225])
        | uu____6241 ->
            let uu____6243 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____6243]
         in
      let uu____6259 =
        let uu____6272 =
          let uu____6273 = FStar_Syntax_Subst.compress t  in
          uu____6273.FStar_Syntax_Syntax.n  in
        match uu____6272 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____6300 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____6300 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____6329;
                        FStar_Syntax_Syntax.effect_name = uu____6330;
                        FStar_Syntax_Syntax.result_typ = uu____6331;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____6333)::(post,uu____6335)::(pats,uu____6337)::[];
                        FStar_Syntax_Syntax.flags = uu____6338;_}
                      ->
                      let uu____6370 = lemma_pats pats  in
                      (binders1, pre, post, uu____6370)
                  | uu____6383 -> failwith "impos"))
        | uu____6396 -> failwith "Impos"  in
      match uu____6259 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___136_6432 = env  in
            {
              bindings = (uu___136_6432.bindings);
              depth = (uu___136_6432.depth);
              tcenv = (uu___136_6432.tcenv);
              warn = (uu___136_6432.warn);
              cache = (uu___136_6432.cache);
              nolabels = (uu___136_6432.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___136_6432.encode_non_total_function_typ);
              current_module_name = (uu___136_6432.current_module_name)
            }  in
          let uu____6433 = encode_binders None binders env1  in
          (match uu____6433 with
           | (vars,guards,env2,decls,uu____6448) ->
               let uu____6455 =
                 let uu____6462 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6484 =
                             let uu____6489 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2))
                                in
                             FStar_All.pipe_right uu____6489 FStar_List.unzip
                              in
                           match uu____6484 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____6462 FStar_List.unzip  in
               (match uu____6455 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let env3 =
                      let uu___137_6547 = env2  in
                      {
                        bindings = (uu___137_6547.bindings);
                        depth = (uu___137_6547.depth);
                        tcenv = (uu___137_6547.tcenv);
                        warn = (uu___137_6547.warn);
                        cache = (uu___137_6547.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___137_6547.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___137_6547.encode_non_total_function_typ);
                        current_module_name =
                          (uu___137_6547.current_module_name)
                      }  in
                    let uu____6548 =
                      let uu____6551 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____6551 env3  in
                    (match uu____6548 with
                     | (pre1,decls'') ->
                         let uu____6556 =
                           let uu____6559 = FStar_Syntax_Util.unmeta post  in
                           encode_formula uu____6559 env3  in
                         (match uu____6556 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____6566 =
                                let uu____6567 =
                                  let uu____6573 =
                                    let uu____6574 =
                                      let uu____6577 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____6577, post1)  in
                                    FStar_SMTEncoding_Util.mkImp uu____6574
                                     in
                                  (pats, vars, uu____6573)  in
                                FStar_SMTEncoding_Util.mkForall uu____6567
                                 in
                              (uu____6566, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6590 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____6590
        then
          let uu____6591 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____6592 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6591 uu____6592
        else ()  in
      let enc f r l =
        let uu____6619 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6632 = encode_term (fst x) env  in
                 match uu____6632 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____6619 with
        | (decls,args) ->
            let uu____6649 =
              let uu___138_6650 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___138_6650.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___138_6650.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6649, decls)
         in
      let const_op f r uu____6675 = let uu____6684 = f r  in (uu____6684, [])
         in
      let un_op f l =
        let uu____6700 = FStar_List.hd l  in FStar_All.pipe_left f uu____6700
         in
      let bin_op f uu___112_6713 =
        match uu___112_6713 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6721 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____6748 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6757  ->
                 match uu____6757 with
                 | (t,uu____6765) ->
                     let uu____6766 = encode_formula t env  in
                     (match uu____6766 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____6748 with
        | (decls,phis) ->
            let uu____6783 =
              let uu___139_6784 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6784.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6784.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____6783, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____6823  ->
               match uu____6823 with
               | (a,q) ->
                   (match q with
                    | Some (FStar_Syntax_Syntax.Implicit uu____6837) -> false
                    | uu____6838 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____6851 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____6851
        else
          (let uu____6866 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____6866 r rf)
         in
      let mk_imp1 r uu___113_6885 =
        match uu___113_6885 with
        | (lhs,uu____6889)::(rhs,uu____6891)::[] ->
            let uu____6912 = encode_formula rhs env  in
            (match uu____6912 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6921) ->
                      (l1, decls1)
                  | uu____6924 ->
                      let uu____6925 = encode_formula lhs env  in
                      (match uu____6925 with
                       | (l2,decls2) ->
                           let uu____6932 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____6932, (FStar_List.append decls1 decls2)))))
        | uu____6934 -> failwith "impossible"  in
      let mk_ite r uu___114_6949 =
        match uu___114_6949 with
        | (guard,uu____6953)::(_then,uu____6955)::(_else,uu____6957)::[] ->
            let uu____6986 = encode_formula guard env  in
            (match uu____6986 with
             | (g,decls1) ->
                 let uu____6993 = encode_formula _then env  in
                 (match uu____6993 with
                  | (t,decls2) ->
                      let uu____7000 = encode_formula _else env  in
                      (match uu____7000 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____7009 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____7028 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l  in
        f uu____7028  in
      let connectives =
        let uu____7040 =
          let uu____7049 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Syntax_Const.and_lid, uu____7049)  in
        let uu____7062 =
          let uu____7072 =
            let uu____7081 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Syntax_Const.or_lid, uu____7081)  in
          let uu____7094 =
            let uu____7104 =
              let uu____7114 =
                let uu____7123 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Syntax_Const.iff_lid, uu____7123)  in
              let uu____7136 =
                let uu____7146 =
                  let uu____7156 =
                    let uu____7165 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Syntax_Const.not_lid, uu____7165)  in
                  [uu____7156;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____7146  in
              uu____7114 :: uu____7136  in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____7104  in
          uu____7072 :: uu____7094  in
        uu____7040 :: uu____7062  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____7381 = encode_formula phi' env  in
            (match uu____7381 with
             | (phi2,decls) ->
                 let uu____7388 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____7388, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____7389 ->
            let uu____7394 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____7394 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____7423 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____7423 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____7431;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____7433;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____7449 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____7449 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____7481::(x,uu____7483)::(t,uu____7485)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7519 = encode_term x env  in
                 (match uu____7519 with
                  | (x1,decls) ->
                      let uu____7526 = encode_term t env  in
                      (match uu____7526 with
                       | (t1,decls') ->
                           let uu____7533 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____7533, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7537)::(msg,uu____7539)::(phi2,uu____7541)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7575 =
                   let uu____7578 =
                     let uu____7579 = FStar_Syntax_Subst.compress r  in
                     uu____7579.FStar_Syntax_Syntax.n  in
                   let uu____7582 =
                     let uu____7583 = FStar_Syntax_Subst.compress msg  in
                     uu____7583.FStar_Syntax_Syntax.n  in
                   (uu____7578, uu____7582)  in
                 (match uu____7575 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7590))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1
                         in
                      fallback phi3
                  | uu____7606 -> fallback phi2)
             | uu____7609 when head_redex env head2 ->
                 let uu____7617 = whnf env phi1  in
                 encode_formula uu____7617 env
             | uu____7618 ->
                 let uu____7626 = encode_term phi1 env  in
                 (match uu____7626 with
                  | (tt,decls) ->
                      let uu____7633 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___140_7634 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___140_7634.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___140_7634.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____7633, decls)))
        | uu____7637 ->
            let uu____7638 = encode_term phi1 env  in
            (match uu____7638 with
             | (tt,decls) ->
                 let uu____7645 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___141_7646 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___141_7646.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___141_7646.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____7645, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____7673 = encode_binders None bs env1  in
        match uu____7673 with
        | (vars,guards,env2,decls,uu____7695) ->
            let uu____7702 =
              let uu____7709 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7732 =
                          let uu____7737 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7751  ->
                                    match uu____7751 with
                                    | (t,uu____7757) ->
                                        encode_term t
                                          (let uu___142_7758 = env2  in
                                           {
                                             bindings =
                                               (uu___142_7758.bindings);
                                             depth = (uu___142_7758.depth);
                                             tcenv = (uu___142_7758.tcenv);
                                             warn = (uu___142_7758.warn);
                                             cache = (uu___142_7758.cache);
                                             nolabels =
                                               (uu___142_7758.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___142_7758.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___142_7758.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____7737 FStar_List.unzip
                           in
                        match uu____7732 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____7709 FStar_List.unzip  in
            (match uu____7702 with
             | (pats,decls') ->
                 let uu____7810 = encode_formula body env2  in
                 (match uu____7810 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7829;
                             FStar_SMTEncoding_Term.rng = uu____7830;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7838 -> guards  in
                      let uu____7841 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____7841, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7875  ->
                   match uu____7875 with
                   | (x,uu____7879) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7885 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7891 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____7891) uu____7885 tl1
                in
             let uu____7893 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7905  ->
                       match uu____7905 with
                       | (b,uu____7909) ->
                           let uu____7910 = FStar_Util.set_mem b pat_vars  in
                           Prims.op_Negation uu____7910))
                in
             (match uu____7893 with
              | None  -> ()
              | Some (x,uu____7914) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____7924 =
                    let uu____7925 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7925
                     in
                  FStar_Errors.warn pos uu____7924)
          in
       let uu____7926 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____7926 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7932 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7968  ->
                     match uu____7968 with
                     | (l,uu____7978) -> FStar_Ident.lid_equals op l))
              in
           (match uu____7932 with
            | None  -> fallback phi1
            | Some (uu____8001,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8030 = encode_q_body env vars pats body  in
             match uu____8030 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____8056 =
                     let uu____8062 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____8062)  in
                   FStar_SMTEncoding_Term.mkForall uu____8056
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____8074 = encode_q_body env vars pats body  in
             match uu____8074 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____8099 =
                   let uu____8100 =
                     let uu____8106 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____8106)  in
                   FStar_SMTEncoding_Term.mkExists uu____8100
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____8099, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl
          Prims.list)
    ;
  is: FStar_Ident.lident -> Prims.bool }
let __proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term * FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let __proj__Mkprims_t__item__is : prims_t -> FStar_Ident.lident -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let prims : prims_t =
  let uu____8185 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____8185 with
  | (asym,a) ->
      let uu____8190 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____8190 with
       | (xsym,x) ->
           let uu____8195 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____8195 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____8225 =
                      let uu____8231 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd)
                         in
                      (x1, uu____8231, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____8225  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None)
                     in
                  let xapp =
                    let uu____8246 =
                      let uu____8250 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____8250)  in
                    FStar_SMTEncoding_Util.mkApp uu____8246  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____8258 =
                    let uu____8260 =
                      let uu____8262 =
                        let uu____8264 =
                          let uu____8265 =
                            let uu____8269 =
                              let uu____8270 =
                                let uu____8276 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____8276)  in
                              FStar_SMTEncoding_Util.mkForall uu____8270  in
                            (uu____8269, None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____8265  in
                        let uu____8285 =
                          let uu____8287 =
                            let uu____8288 =
                              let uu____8292 =
                                let uu____8293 =
                                  let uu____8299 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____8299)  in
                                FStar_SMTEncoding_Util.mkForall uu____8293
                                 in
                              (uu____8292,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____8288  in
                          [uu____8287]  in
                        uu____8264 :: uu____8285  in
                      xtok_decl :: uu____8262  in
                    xname_decl :: uu____8260  in
                  (xtok1, uu____8258)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____8348 =
                    let uu____8356 =
                      let uu____8362 =
                        let uu____8363 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____8363
                         in
                      quant axy uu____8362  in
                    (FStar_Syntax_Const.op_Eq, uu____8356)  in
                  let uu____8369 =
                    let uu____8378 =
                      let uu____8386 =
                        let uu____8392 =
                          let uu____8393 =
                            let uu____8394 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____8394  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____8393
                           in
                        quant axy uu____8392  in
                      (FStar_Syntax_Const.op_notEq, uu____8386)  in
                    let uu____8400 =
                      let uu____8409 =
                        let uu____8417 =
                          let uu____8423 =
                            let uu____8424 =
                              let uu____8425 =
                                let uu____8428 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____8429 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____8428, uu____8429)  in
                              FStar_SMTEncoding_Util.mkLT uu____8425  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____8424
                             in
                          quant xy uu____8423  in
                        (FStar_Syntax_Const.op_LT, uu____8417)  in
                      let uu____8435 =
                        let uu____8444 =
                          let uu____8452 =
                            let uu____8458 =
                              let uu____8459 =
                                let uu____8460 =
                                  let uu____8463 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____8464 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____8463, uu____8464)  in
                                FStar_SMTEncoding_Util.mkLTE uu____8460  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____8459
                               in
                            quant xy uu____8458  in
                          (FStar_Syntax_Const.op_LTE, uu____8452)  in
                        let uu____8470 =
                          let uu____8479 =
                            let uu____8487 =
                              let uu____8493 =
                                let uu____8494 =
                                  let uu____8495 =
                                    let uu____8498 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____8499 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____8498, uu____8499)  in
                                  FStar_SMTEncoding_Util.mkGT uu____8495  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____8494
                                 in
                              quant xy uu____8493  in
                            (FStar_Syntax_Const.op_GT, uu____8487)  in
                          let uu____8505 =
                            let uu____8514 =
                              let uu____8522 =
                                let uu____8528 =
                                  let uu____8529 =
                                    let uu____8530 =
                                      let uu____8533 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____8534 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____8533, uu____8534)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____8530
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8529
                                   in
                                quant xy uu____8528  in
                              (FStar_Syntax_Const.op_GTE, uu____8522)  in
                            let uu____8540 =
                              let uu____8549 =
                                let uu____8557 =
                                  let uu____8563 =
                                    let uu____8564 =
                                      let uu____8565 =
                                        let uu____8568 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____8569 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____8568, uu____8569)  in
                                      FStar_SMTEncoding_Util.mkSub uu____8565
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8564
                                     in
                                  quant xy uu____8563  in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8557)
                                 in
                              let uu____8575 =
                                let uu____8584 =
                                  let uu____8592 =
                                    let uu____8598 =
                                      let uu____8599 =
                                        let uu____8600 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8600
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8599
                                       in
                                    quant qx uu____8598  in
                                  (FStar_Syntax_Const.op_Minus, uu____8592)
                                   in
                                let uu____8606 =
                                  let uu____8615 =
                                    let uu____8623 =
                                      let uu____8629 =
                                        let uu____8630 =
                                          let uu____8631 =
                                            let uu____8634 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____8635 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____8634, uu____8635)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8631
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8630
                                         in
                                      quant xy uu____8629  in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8623)
                                     in
                                  let uu____8641 =
                                    let uu____8650 =
                                      let uu____8658 =
                                        let uu____8664 =
                                          let uu____8665 =
                                            let uu____8666 =
                                              let uu____8669 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____8670 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____8669, uu____8670)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8666
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8665
                                           in
                                        quant xy uu____8664  in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8658)
                                       in
                                    let uu____8676 =
                                      let uu____8685 =
                                        let uu____8693 =
                                          let uu____8699 =
                                            let uu____8700 =
                                              let uu____8701 =
                                                let uu____8704 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____8705 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____8704, uu____8705)  in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8701
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8700
                                             in
                                          quant xy uu____8699  in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8693)
                                         in
                                      let uu____8711 =
                                        let uu____8720 =
                                          let uu____8728 =
                                            let uu____8734 =
                                              let uu____8735 =
                                                let uu____8736 =
                                                  let uu____8739 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____8740 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____8739, uu____8740)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8736
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8735
                                               in
                                            quant xy uu____8734  in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8728)
                                           in
                                        let uu____8746 =
                                          let uu____8755 =
                                            let uu____8763 =
                                              let uu____8769 =
                                                let uu____8770 =
                                                  let uu____8771 =
                                                    let uu____8774 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____8775 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____8774, uu____8775)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8771
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8770
                                                 in
                                              quant xy uu____8769  in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8763)
                                             in
                                          let uu____8781 =
                                            let uu____8790 =
                                              let uu____8798 =
                                                let uu____8804 =
                                                  let uu____8805 =
                                                    let uu____8806 =
                                                      let uu____8809 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____8810 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____8809,
                                                        uu____8810)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8806
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8805
                                                   in
                                                quant xy uu____8804  in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8798)
                                               in
                                            let uu____8816 =
                                              let uu____8825 =
                                                let uu____8833 =
                                                  let uu____8839 =
                                                    let uu____8840 =
                                                      let uu____8841 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8841
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8840
                                                     in
                                                  quant qx uu____8839  in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8833)
                                                 in
                                              [uu____8825]  in
                                            uu____8790 :: uu____8816  in
                                          uu____8755 :: uu____8781  in
                                        uu____8720 :: uu____8746  in
                                      uu____8685 :: uu____8711  in
                                    uu____8650 :: uu____8676  in
                                  uu____8615 :: uu____8641  in
                                uu____8584 :: uu____8606  in
                              uu____8549 :: uu____8575  in
                            uu____8514 :: uu____8540  in
                          uu____8479 :: uu____8505  in
                        uu____8444 :: uu____8470  in
                      uu____8409 :: uu____8435  in
                    uu____8378 :: uu____8400  in
                  uu____8348 :: uu____8369  in
                let mk1 l v1 =
                  let uu____8969 =
                    let uu____8974 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____9006  ->
                              match uu____9006 with
                              | (l',uu____9015) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____8974
                      (FStar_Option.map
                         (fun uu____9048  ->
                            match uu____9048 with | (uu____9059,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____8969 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____9100  ->
                          match uu____9100 with
                          | (l',uu____9109) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string * FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____9138 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____9138 with
        | (xxsym,xx) ->
            let uu____9143 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____9143 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____9151 =
                   let uu____9155 =
                     let uu____9156 =
                       let uu____9162 =
                         let uu____9163 =
                           let uu____9166 =
                             let uu____9167 =
                               let uu____9170 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____9170)  in
                             FStar_SMTEncoding_Util.mkEq uu____9167  in
                           (xx_has_type, uu____9166)  in
                         FStar_SMTEncoding_Util.mkImp uu____9163  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____9162)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____9156  in
                   let uu____9183 =
                     let uu____9184 =
                       let uu____9185 =
                         let uu____9186 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____9186  in
                       Prims.strcat module_name uu____9185  in
                     varops.mk_unique uu____9184  in
                   (uu____9155, (Some "pretyping"), uu____9183)  in
                 FStar_SMTEncoding_Util.mkAssume uu____9151)
  
let primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____9220 =
      let uu____9221 =
        let uu____9225 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____9225, (Some "unit typing"), "unit_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____9221  in
    let uu____9227 =
      let uu____9229 =
        let uu____9230 =
          let uu____9234 =
            let uu____9235 =
              let uu____9241 =
                let uu____9242 =
                  let uu____9245 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____9245)  in
                FStar_SMTEncoding_Util.mkImp uu____9242  in
              ([[typing_pred]], [xx], uu____9241)  in
            mkForall_fuel uu____9235  in
          (uu____9234, (Some "unit inversion"), "unit_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____9230  in
      [uu____9229]  in
    uu____9220 :: uu____9227  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____9273 =
      let uu____9274 =
        let uu____9278 =
          let uu____9279 =
            let uu____9285 =
              let uu____9288 =
                let uu____9290 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____9290]  in
              [uu____9288]  in
            let uu____9293 =
              let uu____9294 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____9294 tt  in
            (uu____9285, [bb], uu____9293)  in
          FStar_SMTEncoding_Util.mkForall uu____9279  in
        (uu____9278, (Some "bool typing"), "bool_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____9274  in
    let uu____9305 =
      let uu____9307 =
        let uu____9308 =
          let uu____9312 =
            let uu____9313 =
              let uu____9319 =
                let uu____9320 =
                  let uu____9323 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x  in
                  (typing_pred, uu____9323)  in
                FStar_SMTEncoding_Util.mkImp uu____9320  in
              ([[typing_pred]], [xx], uu____9319)  in
            mkForall_fuel uu____9313  in
          (uu____9312, (Some "bool inversion"), "bool_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____9308  in
      [uu____9307]  in
    uu____9273 :: uu____9305  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____9357 =
        let uu____9358 =
          let uu____9362 =
            let uu____9364 =
              let uu____9366 =
                let uu____9368 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____9369 =
                  let uu____9371 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____9371]  in
                uu____9368 :: uu____9369  in
              tt :: uu____9366  in
            tt :: uu____9364  in
          ("Prims.Precedes", uu____9362)  in
        FStar_SMTEncoding_Util.mkApp uu____9358  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9357  in
    let precedes_y_x =
      let uu____9374 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____9374  in
    let uu____9376 =
      let uu____9377 =
        let uu____9381 =
          let uu____9382 =
            let uu____9388 =
              let uu____9391 =
                let uu____9393 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____9393]  in
              [uu____9391]  in
            let uu____9396 =
              let uu____9397 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____9397 tt  in
            (uu____9388, [bb], uu____9396)  in
          FStar_SMTEncoding_Util.mkForall uu____9382  in
        (uu____9381, (Some "int typing"), "int_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____9377  in
    let uu____9408 =
      let uu____9410 =
        let uu____9411 =
          let uu____9415 =
            let uu____9416 =
              let uu____9422 =
                let uu____9423 =
                  let uu____9426 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x  in
                  (typing_pred, uu____9426)  in
                FStar_SMTEncoding_Util.mkImp uu____9423  in
              ([[typing_pred]], [xx], uu____9422)  in
            mkForall_fuel uu____9416  in
          (uu____9415, (Some "int inversion"), "int_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____9411  in
      let uu____9439 =
        let uu____9441 =
          let uu____9442 =
            let uu____9446 =
              let uu____9447 =
                let uu____9453 =
                  let uu____9454 =
                    let uu____9457 =
                      let uu____9458 =
                        let uu____9460 =
                          let uu____9462 =
                            let uu____9464 =
                              let uu____9465 =
                                let uu____9468 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____9469 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____9468, uu____9469)  in
                              FStar_SMTEncoding_Util.mkGT uu____9465  in
                            let uu____9470 =
                              let uu____9472 =
                                let uu____9473 =
                                  let uu____9476 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____9477 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____9476, uu____9477)  in
                                FStar_SMTEncoding_Util.mkGTE uu____9473  in
                              let uu____9478 =
                                let uu____9480 =
                                  let uu____9481 =
                                    let uu____9484 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____9485 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____9484, uu____9485)  in
                                  FStar_SMTEncoding_Util.mkLT uu____9481  in
                                [uu____9480]  in
                              uu____9472 :: uu____9478  in
                            uu____9464 :: uu____9470  in
                          typing_pred_y :: uu____9462  in
                        typing_pred :: uu____9460  in
                      FStar_SMTEncoding_Util.mk_and_l uu____9458  in
                    (uu____9457, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____9454  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____9453)
                 in
              mkForall_fuel uu____9447  in
            (uu____9446, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____9442  in
        [uu____9441]  in
      uu____9410 :: uu____9439  in
    uu____9376 :: uu____9408  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____9515 =
      let uu____9516 =
        let uu____9520 =
          let uu____9521 =
            let uu____9527 =
              let uu____9530 =
                let uu____9532 = FStar_SMTEncoding_Term.boxString b  in
                [uu____9532]  in
              [uu____9530]  in
            let uu____9535 =
              let uu____9536 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____9536 tt  in
            (uu____9527, [bb], uu____9535)  in
          FStar_SMTEncoding_Util.mkForall uu____9521  in
        (uu____9520, (Some "string typing"), "string_typing")  in
      FStar_SMTEncoding_Util.mkAssume uu____9516  in
    let uu____9547 =
      let uu____9549 =
        let uu____9550 =
          let uu____9554 =
            let uu____9555 =
              let uu____9561 =
                let uu____9562 =
                  let uu____9565 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x  in
                  (typing_pred, uu____9565)  in
                FStar_SMTEncoding_Util.mkImp uu____9562  in
              ([[typing_pred]], [xx], uu____9561)  in
            mkForall_fuel uu____9555  in
          (uu____9554, (Some "string inversion"), "string_inversion")  in
        FStar_SMTEncoding_Util.mkAssume uu____9550  in
      [uu____9549]  in
    uu____9515 :: uu____9547  in
  let mk_ref1 env reft_name uu____9587 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort)  in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let refa =
      let uu____9598 =
        let uu____9602 =
          let uu____9604 = FStar_SMTEncoding_Util.mkFreeV aa  in [uu____9604]
           in
        (reft_name, uu____9602)  in
      FStar_SMTEncoding_Util.mkApp uu____9598  in
    let refb =
      let uu____9607 =
        let uu____9611 =
          let uu____9613 = FStar_SMTEncoding_Util.mkFreeV bb  in [uu____9613]
           in
        (reft_name, uu____9611)  in
      FStar_SMTEncoding_Util.mkApp uu____9607  in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa  in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb  in
    let uu____9617 =
      let uu____9618 =
        let uu____9622 =
          let uu____9623 =
            let uu____9629 =
              let uu____9630 =
                let uu____9633 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x
                   in
                (typing_pred, uu____9633)  in
              FStar_SMTEncoding_Util.mkImp uu____9630  in
            ([[typing_pred]], [xx; aa], uu____9629)  in
          mkForall_fuel uu____9623  in
        (uu____9622, (Some "ref inversion"), "ref_inversion")  in
      FStar_SMTEncoding_Util.mkAssume uu____9618  in
    [uu____9617]  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____9673 =
      let uu____9674 =
        let uu____9678 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____9678, (Some "False interpretation"), "false_interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9674  in
    [uu____9673]  in
  let mk_and_interp env conj uu____9689 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9706 =
      let uu____9707 =
        let uu____9711 =
          let uu____9712 =
            let uu____9718 =
              let uu____9719 =
                let uu____9722 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____9722, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9719  in
            ([[l_and_a_b]], [aa; bb], uu____9718)  in
          FStar_SMTEncoding_Util.mkForall uu____9712  in
        (uu____9711, (Some "/\\ interpretation"), "l_and-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9707  in
    [uu____9706]  in
  let mk_or_interp env disj uu____9746 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9763 =
      let uu____9764 =
        let uu____9768 =
          let uu____9769 =
            let uu____9775 =
              let uu____9776 =
                let uu____9779 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____9779, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9776  in
            ([[l_or_a_b]], [aa; bb], uu____9775)  in
          FStar_SMTEncoding_Util.mkForall uu____9769  in
        (uu____9768, (Some "\\/ interpretation"), "l_or-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9764  in
    [uu____9763]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____9820 =
      let uu____9821 =
        let uu____9825 =
          let uu____9826 =
            let uu____9832 =
              let uu____9833 =
                let uu____9836 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9836, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9833  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9832)  in
          FStar_SMTEncoding_Util.mkForall uu____9826  in
        (uu____9825, (Some "Eq2 interpretation"), "eq2-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9821  in
    [uu____9820]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____9883 =
      let uu____9884 =
        let uu____9888 =
          let uu____9889 =
            let uu____9895 =
              let uu____9896 =
                let uu____9899 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____9899, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9896  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9895)  in
          FStar_SMTEncoding_Util.mkForall uu____9889  in
        (uu____9888, (Some "Eq3 interpretation"), "eq3-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9884  in
    [uu____9883]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____9944 =
      let uu____9945 =
        let uu____9949 =
          let uu____9950 =
            let uu____9956 =
              let uu____9957 =
                let uu____9960 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____9960, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____9957  in
            ([[l_imp_a_b]], [aa; bb], uu____9956)  in
          FStar_SMTEncoding_Util.mkForall uu____9950  in
        (uu____9949, (Some "==> interpretation"), "l_imp-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____9945  in
    [uu____9944]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____10001 =
      let uu____10002 =
        let uu____10006 =
          let uu____10007 =
            let uu____10013 =
              let uu____10014 =
                let uu____10017 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____10017, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____10014  in
            ([[l_iff_a_b]], [aa; bb], uu____10013)  in
          FStar_SMTEncoding_Util.mkForall uu____10007  in
        (uu____10006, (Some "<==> interpretation"), "l_iff-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____10002  in
    [uu____10001]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____10051 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____10051  in
    let uu____10053 =
      let uu____10054 =
        let uu____10058 =
          let uu____10059 =
            let uu____10065 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____10065)  in
          FStar_SMTEncoding_Util.mkForall uu____10059  in
        (uu____10058, (Some "not interpretation"), "l_not-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____10054  in
    [uu____10053]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b])  in
    let valid_b_x =
      let uu____10105 =
        let uu____10109 =
          let uu____10111 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____10111]  in
        ("Valid", uu____10109)  in
      FStar_SMTEncoding_Util.mkApp uu____10105  in
    let uu____10113 =
      let uu____10114 =
        let uu____10118 =
          let uu____10119 =
            let uu____10125 =
              let uu____10126 =
                let uu____10129 =
                  let uu____10130 =
                    let uu____10136 =
                      let uu____10139 =
                        let uu____10141 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____10141]  in
                      [uu____10139]  in
                    let uu____10144 =
                      let uu____10145 =
                        let uu____10148 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____10148, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____10145  in
                    (uu____10136, [xx1], uu____10144)  in
                  FStar_SMTEncoding_Util.mkForall uu____10130  in
                (uu____10129, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____10126  in
            ([[l_forall_a_b]], [aa; bb], uu____10125)  in
          FStar_SMTEncoding_Util.mkForall uu____10119  in
        (uu____10118, (Some "forall interpretation"), "forall-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____10114  in
    [uu____10113]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b])  in
    let valid_b_x =
      let uu____10199 =
        let uu____10203 =
          let uu____10205 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____10205]  in
        ("Valid", uu____10203)  in
      FStar_SMTEncoding_Util.mkApp uu____10199  in
    let uu____10207 =
      let uu____10208 =
        let uu____10212 =
          let uu____10213 =
            let uu____10219 =
              let uu____10220 =
                let uu____10223 =
                  let uu____10224 =
                    let uu____10230 =
                      let uu____10233 =
                        let uu____10235 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____10235]  in
                      [uu____10233]  in
                    let uu____10238 =
                      let uu____10239 =
                        let uu____10242 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____10242, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____10239  in
                    (uu____10230, [xx1], uu____10238)  in
                  FStar_SMTEncoding_Util.mkExists uu____10224  in
                (uu____10223, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____10220  in
            ([[l_exists_a_b]], [aa; bb], uu____10219)  in
          FStar_SMTEncoding_Util.mkForall uu____10213  in
        (uu____10212, (Some "exists interpretation"), "exists-interp")  in
      FStar_SMTEncoding_Util.mkAssume uu____10208  in
    [uu____10207]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____10278 =
      let uu____10279 =
        let uu____10283 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____10284 = varops.mk_unique "typing_range_const"  in
        (uu____10283, (Some "Range_const typing"), uu____10284)  in
      FStar_SMTEncoding_Util.mkAssume uu____10279  in
    [uu____10278]  in
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
    (FStar_Syntax_Const.range_lid, mk_range_interp)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____10546 =
            FStar_Util.find_opt
              (fun uu____10564  ->
                 match uu____10564 with
                 | (l,uu____10574) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____10546 with
          | None  -> []
          | Some (uu____10596,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____10636 = encode_function_type_as_formula t env  in
        match uu____10636 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let encode_free_var :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
               in
            let uu____10673 =
              (let uu____10674 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm)
                  in
               FStar_All.pipe_left Prims.op_Negation uu____10674) ||
                (FStar_Syntax_Util.is_lemma t_norm)
               in
            if uu____10673
            then
              let uu____10678 = new_term_constant_and_tok_from_lid env lid
                 in
              match uu____10678 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10690 =
                      let uu____10691 = FStar_Syntax_Subst.compress t_norm
                         in
                      uu____10691.FStar_Syntax_Syntax.n  in
                    match uu____10690 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10696) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10713  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10716 -> []  in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function"))
                     in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function"))
                     in
                  ([d; dd], env1)
            else
              (let uu____10725 = prims.is lid  in
               if uu____10725
               then
                 let vname = varops.new_fvar lid  in
                 let uu____10730 = prims.mk lid vname  in
                 match uu____10730 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok)  in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims"  in
                  let uu____10745 =
                    let uu____10751 = curried_arrow_formals_comp t_norm  in
                    match uu____10751 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10762 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp
                             in
                          if uu____10762
                          then
                            let uu____10763 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___143_10764 = env.tcenv  in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___143_10764.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___143_10764.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___143_10764.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___143_10764.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___143_10764.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___143_10764.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___143_10764.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___143_10764.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___143_10764.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___143_10764.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___143_10764.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___143_10764.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___143_10764.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___143_10764.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___143_10764.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___143_10764.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___143_10764.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___143_10764.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___143_10764.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___143_10764.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___143_10764.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___143_10764.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___143_10764.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___143_10764.FStar_TypeChecker_Env.proof_ns);
                                   FStar_TypeChecker_Env.synth =
                                     (uu___143_10764.FStar_TypeChecker_Env.synth);
                                   FStar_TypeChecker_Env.is_native_tactic =
                                     (uu___143_10764.FStar_TypeChecker_Env.is_native_tactic)
                                 }) comp FStar_Syntax_Syntax.U_unknown
                               in
                            FStar_Syntax_Syntax.mk_Total uu____10763
                          else comp  in
                        if encode_non_total_function_typ
                        then
                          let uu____10771 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1
                             in
                          (args, uu____10771)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1)))
                     in
                  match uu____10745 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10798 =
                        new_term_constant_and_tok_from_lid env lid  in
                      (match uu____10798 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10811 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, [])
                              in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10835  ->
                                     match uu___115_10835 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10838 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10838 with
                                          | (uu____10849,(xxsym,uu____10851))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let uu____10861 =
                                                let uu____10862 =
                                                  let uu____10866 =
                                                    let uu____10867 =
                                                      let uu____10873 =
                                                        let uu____10874 =
                                                          let uu____10877 =
                                                            let uu____10878 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx
                                                               in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10878
                                                             in
                                                          (vapp, uu____10877)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10874
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10873)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10867
                                                     in
                                                  (uu____10866,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str)))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10862
                                                 in
                                              [uu____10861])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10889 =
                                           FStar_Util.prefix vars  in
                                         (match uu____10889 with
                                          | (uu____10900,(xxsym,uu____10902))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort)
                                                 in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                }  in
                                              let tp_name =
                                                mk_term_projector_name d f1
                                                 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx])
                                                 in
                                              let uu____10916 =
                                                let uu____10917 =
                                                  let uu____10921 =
                                                    let uu____10922 =
                                                      let uu____10928 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app)
                                                         in
                                                      ([[vapp]], vars,
                                                        uu____10928)
                                                       in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10922
                                                     in
                                                  (uu____10921,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name))
                                                   in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10917
                                                 in
                                              [uu____10916])
                                     | uu____10937 -> []))
                              in
                           let uu____10938 = encode_binders None formals env1
                              in
                           (match uu____10938 with
                            | (vars,guards,env',decls1,uu____10954) ->
                                let uu____10961 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10966 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards
                                         in
                                      (uu____10966, decls1)
                                  | Some p ->
                                      let uu____10968 = encode_formula p env'
                                         in
                                      (match uu____10968 with
                                       | (g,ds) ->
                                           let uu____10975 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards)
                                              in
                                           (uu____10975,
                                             (FStar_List.append decls1 ds)))
                                   in
                                (match uu____10961 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars  in
                                     let vapp =
                                       let uu____10984 =
                                         let uu____10988 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars
                                            in
                                         (vname, uu____10988)  in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10984
                                        in
                                     let uu____10993 =
                                       let vname_decl =
                                         let uu____10998 =
                                           let uu____11004 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____11009  ->
                                                     FStar_SMTEncoding_Term.Term_sort))
                                              in
                                           (vname, uu____11004,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None)
                                            in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10998
                                          in
                                       let uu____11014 =
                                         let env2 =
                                           let uu___144_11018 = env1  in
                                           {
                                             bindings =
                                               (uu___144_11018.bindings);
                                             depth = (uu___144_11018.depth);
                                             tcenv = (uu___144_11018.tcenv);
                                             warn = (uu___144_11018.warn);
                                             cache = (uu___144_11018.cache);
                                             nolabels =
                                               (uu___144_11018.nolabels);
                                             use_zfuel_name =
                                               (uu___144_11018.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___144_11018.current_module_name)
                                           }  in
                                         let uu____11019 =
                                           let uu____11020 =
                                             head_normal env2 tt  in
                                           Prims.op_Negation uu____11020  in
                                         if uu____11019
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm
                                          in
                                       match uu____11014 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____11030::uu____11031 ->
                                                 let ff =
                                                   ("ty",
                                                     FStar_SMTEncoding_Term.Term_sort)
                                                    in
                                                 let f =
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                     ff
                                                    in
                                                 let vtok_app_l =
                                                   mk_Apply vtok_tm [ff]  in
                                                 let vtok_app_r =
                                                   mk_Apply f
                                                     [(vtok,
                                                        FStar_SMTEncoding_Term.Term_sort)]
                                                    in
                                                 let guarded_tok_typing =
                                                   let uu____11054 =
                                                     let uu____11060 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing
                                                        in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____11060)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____11054
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____11074 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                              in
                                           let uu____11076 =
                                             match formals with
                                             | [] ->
                                                 let uu____11085 =
                                                   let uu____11086 =
                                                     let uu____11088 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort)
                                                        in
                                                     FStar_All.pipe_left
                                                       (fun _0_41  ->
                                                          Some _0_41)
                                                       uu____11088
                                                      in
                                                   push_free_var env1 lid
                                                     vname uu____11086
                                                    in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____11085)
                                             | uu____11091 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None)
                                                    in
                                                 let vtok_fresh =
                                                   let uu____11096 =
                                                     varops.next_id ()  in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____11096
                                                    in
                                                 let name_tok_corr =
                                                   let uu____11098 =
                                                     let uu____11102 =
                                                       let uu____11103 =
                                                         let uu____11109 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp)
                                                            in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____11109)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____11103
                                                        in
                                                     (uu____11102,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____11098
                                                    in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1)
                                              in
                                           (match uu____11076 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2))
                                        in
                                     (match uu____10993 with
                                      | (decls2,env2) ->
                                          let uu____11133 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t
                                               in
                                            let uu____11138 =
                                              encode_term res_t1 env'  in
                                            match uu____11138 with
                                            | (encoded_res_t,decls) ->
                                                let uu____11146 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t
                                                   in
                                                (encoded_res_t, uu____11146,
                                                  decls)
                                             in
                                          (match uu____11133 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____11154 =
                                                   let uu____11158 =
                                                     let uu____11159 =
                                                       let uu____11165 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred)
                                                          in
                                                       ([[vapp]], vars,
                                                         uu____11165)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____11159
                                                      in
                                                   (uu____11158,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname))
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____11154
                                                  in
                                               let freshness =
                                                 let uu____11174 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New)
                                                    in
                                                 if uu____11174
                                                 then
                                                   let uu____11177 =
                                                     let uu____11178 =
                                                       let uu____11184 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd)
                                                          in
                                                       let uu____11190 =
                                                         varops.next_id ()
                                                          in
                                                       (vname, uu____11184,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____11190)
                                                        in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____11178
                                                      in
                                                   let uu____11192 =
                                                     let uu____11194 =
                                                       pretype_axiom env2
                                                         vapp vars
                                                        in
                                                     [uu____11194]  in
                                                   uu____11177 :: uu____11192
                                                 else []  in
                                               let g =
                                                 let uu____11198 =
                                                   let uu____11200 =
                                                     let uu____11202 =
                                                       let uu____11204 =
                                                         let uu____11206 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars
                                                            in
                                                         typingAx ::
                                                           uu____11206
                                                          in
                                                       FStar_List.append
                                                         freshness
                                                         uu____11204
                                                        in
                                                     FStar_List.append decls3
                                                       uu____11202
                                                      in
                                                   FStar_List.append decls2
                                                     uu____11200
                                                    in
                                                 FStar_List.append decls11
                                                   uu____11198
                                                  in
                                               (g, env2))))))))
  
let declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string * FStar_SMTEncoding_Term.term option) *
            FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____11232 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____11232 with
          | None  ->
              let uu____11255 = encode_free_var env x t t_norm []  in
              (match uu____11255 with
               | (decls,env1) ->
                   let uu____11270 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____11270 with
                    | (n1,x',uu____11289) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____11301) -> ((n1, x1), [], env)
  
let encode_top_level_val :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t  in
          let uu____11338 = encode_free_var env lid t tt quals  in
          match uu____11338 with
          | (decls,env1) ->
              let uu____11349 = FStar_Syntax_Util.is_smt_lemma t  in
              if uu____11349
              then
                let uu____11353 =
                  let uu____11355 = encode_smt_lemma env1 lid tt  in
                  FStar_List.append decls uu____11355  in
                (uu____11353, env1)
              else (decls, env1)
  
let encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____11386  ->
                fun lb  ->
                  match uu____11386 with
                  | (decls,env1) ->
                      let uu____11398 =
                        let uu____11402 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val env1 uu____11402
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____11398 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____11417 = FStar_Syntax_Util.head_and_args t  in
    match uu____11417 with
    | (hd1,args) ->
        let uu____11443 =
          let uu____11444 = FStar_Syntax_Util.un_uinst hd1  in
          uu____11444.FStar_Syntax_Syntax.n  in
        (match uu____11443 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____11448,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____11461 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool * FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun uu____11479  ->
      fun quals  ->
        match uu____11479 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____11529 = FStar_Util.first_N nbinders formals  in
              match uu____11529 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11571  ->
                         fun uu____11572  ->
                           match (uu____11571, uu____11572) with
                           | ((formal,uu____11582),(binder,uu____11584)) ->
                               let uu____11589 =
                                 let uu____11594 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____11594)  in
                               FStar_Syntax_Syntax.NT uu____11589) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____11599 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11613  ->
                              match uu____11613 with
                              | (x,i) ->
                                  let uu____11620 =
                                    let uu___145_11621 = x  in
                                    let uu____11622 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___145_11621.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___145_11621.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11622
                                    }  in
                                  (uu____11620, i)))
                       in
                    FStar_All.pipe_right uu____11599
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____11634 =
                      let uu____11636 =
                        let uu____11637 = FStar_Syntax_Subst.subst subst1 t
                           in
                        uu____11637.FStar_Syntax_Syntax.n  in
                      FStar_All.pipe_left (fun _0_42  -> Some _0_42)
                        uu____11636
                       in
                    let uu____11641 =
                      let uu____11642 = FStar_Syntax_Subst.compress body  in
                      let uu____11643 =
                        let uu____11644 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11644
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____11642
                        uu____11643
                       in
                    uu____11641 uu____11634 body.FStar_Syntax_Syntax.pos  in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11686 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____11686
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___146_11687 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___146_11687.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___146_11687.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___146_11687.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___146_11687.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___146_11687.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___146_11687.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___146_11687.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___146_11687.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___146_11687.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___146_11687.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___146_11687.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___146_11687.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___146_11687.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___146_11687.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___146_11687.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___146_11687.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___146_11687.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___146_11687.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___146_11687.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___146_11687.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___146_11687.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___146_11687.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___146_11687.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___146_11687.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___146_11687.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___146_11687.FStar_TypeChecker_Env.is_native_tactic)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____11708 = FStar_Syntax_Util.abs_formals e  in
                match uu____11708 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11742::uu____11743 ->
                         let uu____11751 =
                           let uu____11752 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____11752.FStar_Syntax_Syntax.n  in
                         (match uu____11751 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11779 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____11779 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____11807 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____11807
                                   then
                                     let uu____11830 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____11830 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11878  ->
                                                   fun uu____11879  ->
                                                     match (uu____11878,
                                                             uu____11879)
                                                     with
                                                     | ((x,uu____11889),
                                                        (b,uu____11891)) ->
                                                         let uu____11896 =
                                                           let uu____11901 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____11901)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11896)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____11903 =
                                            let uu____11914 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____11914)
                                             in
                                          (uu____11903, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11954 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____11954 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____12006) ->
                              let uu____12011 =
                                let uu____12022 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                fst uu____12022  in
                              (uu____12011, true)
                          | uu____12055 when Prims.op_Negation norm1 ->
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
                                  env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____12057 ->
                              let uu____12058 =
                                let uu____12059 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____12060 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____12059
                                  uu____12060
                                 in
                              failwith uu____12058)
                     | uu____12073 ->
                         let uu____12074 =
                           let uu____12075 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____12075.FStar_Syntax_Syntax.n  in
                         (match uu____12074 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____12102 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____12102 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____12120 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____12120 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____12168 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____12196 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____12196
               then encode_top_level_vals env bindings quals
               else
                 (let uu____12203 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____12244  ->
                            fun lb  ->
                              match uu____12244 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____12295 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____12295
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____12298 =
                                      let uu____12306 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____12306
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____12298 with
                                    | (tok,decl,env2) ->
                                        let uu____12331 =
                                          let uu____12338 =
                                            let uu____12344 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____12344, tok)  in
                                          uu____12338 :: toks  in
                                        (uu____12331, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____12203 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____12446 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____12451 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____12451 vars)
                            else
                              (let uu____12453 =
                                 let uu____12457 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____12457)  in
                               FStar_SMTEncoding_Util.mkApp uu____12453)
                         in
                      let uu____12462 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_12464  ->
                                 match uu___116_12464 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____12465 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____12468 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____12468)))
                         in
                      if uu____12462
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____12488;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____12490;
                                FStar_Syntax_Syntax.lbeff = uu____12491;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____12532 =
                                 let uu____12536 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm]
                                    in
                                 match uu____12536 with
                                 | (tcenv',uu____12547,e_t) ->
                                     let uu____12551 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12558 -> failwith "Impossible"
                                        in
                                     (match uu____12551 with
                                      | (e1,t_norm1) ->
                                          ((let uu___149_12567 = env1  in
                                            {
                                              bindings =
                                                (uu___149_12567.bindings);
                                              depth = (uu___149_12567.depth);
                                              tcenv = tcenv';
                                              warn = (uu___149_12567.warn);
                                              cache = (uu___149_12567.cache);
                                              nolabels =
                                                (uu___149_12567.nolabels);
                                              use_zfuel_name =
                                                (uu___149_12567.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___149_12567.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___149_12567.current_module_name)
                                            }), e1, t_norm1))
                                  in
                               (match uu____12532 with
                                | (env',e1,t_norm1) ->
                                    let uu____12574 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____12574 with
                                     | ((binders,body,uu____12586,uu____12587),curry)
                                         ->
                                         ((let uu____12594 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____12594
                                           then
                                             let uu____12595 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____12596 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12595 uu____12596
                                           else ());
                                          (let uu____12598 =
                                             encode_binders None binders env'
                                              in
                                           match uu____12598 with
                                           | (vars,guards,env'1,binder_decls,uu____12614)
                                               ->
                                               let body1 =
                                                 let uu____12622 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____12622
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____12625 =
                                                 let uu____12630 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____12630
                                                 then
                                                   let uu____12636 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____12637 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____12636, uu____12637)
                                                 else
                                                   (let uu____12643 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____12643))
                                                  in
                                               (match uu____12625 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12657 =
                                                        let uu____12661 =
                                                          let uu____12662 =
                                                            let uu____12668 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____12668)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12662
                                                           in
                                                        let uu____12674 =
                                                          let uu____12676 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          Some uu____12676
                                                           in
                                                        (uu____12661,
                                                          uu____12674,
                                                          (Prims.strcat
                                                             "equation_" f))
                                                         in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12657
                                                       in
                                                    let uu____12678 =
                                                      let uu____12680 =
                                                        let uu____12682 =
                                                          let uu____12684 =
                                                            let uu____12686 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12686
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12684
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12682
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____12680
                                                       in
                                                    (uu____12678, env1))))))
                           | uu____12689 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12708 = varops.fresh "fuel"  in
                             (uu____12708, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____12711 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12750  ->
                                     fun uu____12751  ->
                                       match (uu____12750, uu____12751) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____12833 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____12833  in
                                           let gtok =
                                             let uu____12835 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____12835  in
                                           let env3 =
                                             let uu____12837 =
                                               let uu____12839 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_43  -> Some _0_43)
                                                 uu____12839
                                                in
                                             push_free_var env2 flid gtok
                                               uu____12837
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____12711 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____12925
                                 t_norm uu____12927 =
                                 match (uu____12925, uu____12927) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12954;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12955;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12972 =
                                       let uu____12976 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm]
                                          in
                                       match uu____12976 with
                                       | (tcenv',uu____12991,e_t) ->
                                           let uu____12995 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____13002 ->
                                                 failwith "Impossible"
                                              in
                                           (match uu____12995 with
                                            | (e1,t_norm1) ->
                                                ((let uu___150_13011 = env2
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___150_13011.bindings);
                                                    depth =
                                                      (uu___150_13011.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___150_13011.warn);
                                                    cache =
                                                      (uu___150_13011.cache);
                                                    nolabels =
                                                      (uu___150_13011.nolabels);
                                                    use_zfuel_name =
                                                      (uu___150_13011.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___150_13011.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___150_13011.current_module_name)
                                                  }), e1, t_norm1))
                                        in
                                     (match uu____12972 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____13021 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____13021
                                            then
                                              let uu____13022 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____13023 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____13024 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____13022 uu____13023
                                                uu____13024
                                            else ());
                                           (let uu____13026 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____13026 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____13048 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____13048
                                                  then
                                                    let uu____13049 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____13050 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____13051 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____13052 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____13049 uu____13050
                                                      uu____13051 uu____13052
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____13056 =
                                                    encode_binders None
                                                      binders env'
                                                     in
                                                  match uu____13056 with
                                                  | (vars,guards,env'1,binder_decls,uu____13074)
                                                      ->
                                                      let decl_g =
                                                        let uu____13082 =
                                                          let uu____13088 =
                                                            let uu____13090 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____13090
                                                             in
                                                          (g, uu____13088,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____13082
                                                         in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g
                                                         in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications"))
                                                         in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars
                                                         in
                                                      let app =
                                                        let uu____13105 =
                                                          let uu____13109 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____13109)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13105
                                                         in
                                                      let gsapp =
                                                        let uu____13115 =
                                                          let uu____13119 =
                                                            let uu____13121 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____13121 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____13119)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13115
                                                         in
                                                      let gmax =
                                                        let uu____13125 =
                                                          let uu____13129 =
                                                            let uu____13131 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____13131 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____13129)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____13125
                                                         in
                                                      let body1 =
                                                        let uu____13135 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____13135
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____13137 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____13137 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____13148
                                                               =
                                                               let uu____13152
                                                                 =
                                                                 let uu____13153
                                                                   =
                                                                   let uu____13161
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13161)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____13153
                                                                  in
                                                               let uu____13172
                                                                 =
                                                                 let uu____13174
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str
                                                                    in
                                                                 Some
                                                                   uu____13174
                                                                  in
                                                               (uu____13152,
                                                                 uu____13172,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13148
                                                              in
                                                           let eqn_f =
                                                             let uu____13177
                                                               =
                                                               let uu____13181
                                                                 =
                                                                 let uu____13182
                                                                   =
                                                                   let uu____13188
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____13188)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13182
                                                                  in
                                                               (uu____13181,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13177
                                                              in
                                                           let eqn_g' =
                                                             let uu____13196
                                                               =
                                                               let uu____13200
                                                                 =
                                                                 let uu____13201
                                                                   =
                                                                   let uu____13207
                                                                    =
                                                                    let uu____13208
                                                                    =
                                                                    let uu____13211
                                                                    =
                                                                    let uu____13212
                                                                    =
                                                                    let uu____13216
                                                                    =
                                                                    let uu____13218
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____13218
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____13216)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____13212
                                                                     in
                                                                    (gsapp,
                                                                    uu____13211)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____13208
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____13207)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____13201
                                                                  in
                                                               (uu____13200,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____13196
                                                              in
                                                           let uu____13230 =
                                                             let uu____13235
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02
                                                                in
                                                             match uu____13235
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____13252)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1
                                                                    in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                    in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____13267
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____13267
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____13270
                                                                    =
                                                                    let uu____13274
                                                                    =
                                                                    let uu____13275
                                                                    =
                                                                    let uu____13281
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13281)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13275
                                                                     in
                                                                    (uu____13274,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13270
                                                                    in
                                                                 let uu____13292
                                                                   =
                                                                   let uu____13296
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp
                                                                     in
                                                                   match uu____13296
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____13304
                                                                    =
                                                                    let uu____13306
                                                                    =
                                                                    let uu____13307
                                                                    =
                                                                    let uu____13311
                                                                    =
                                                                    let uu____13312
                                                                    =
                                                                    let uu____13318
                                                                    =
                                                                    let uu____13319
                                                                    =
                                                                    let uu____13322
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____13322,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____13319
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____13318)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____13312
                                                                     in
                                                                    (uu____13311,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____13307
                                                                     in
                                                                    [uu____13306]
                                                                     in
                                                                    (d3,
                                                                    uu____13304)
                                                                    in
                                                                 (match uu____13292
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                              in
                                                           (match uu____13230
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
                                                                  env02))))))))
                                  in
                               let uu____13357 =
                                 let uu____13364 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____13400  ->
                                      fun uu____13401  ->
                                        match (uu____13400, uu____13401) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____13487 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____13487 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____13364
                                  in
                               (match uu____13357 with
                                | (decls2,eqns,env01) ->
                                    let uu____13527 =
                                      let isDeclFun uu___117_13535 =
                                        match uu___117_13535 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____13536 -> true
                                        | uu____13542 -> false  in
                                      let uu____13543 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____13543
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____13527 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13570 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____13570
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____13603 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____13603 with | None  -> "" | Some l -> l.FStar_Ident.str
         in
      let uu____13606 = encode_sigelt' env se  in
      match uu____13606 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13616 =
                  let uu____13617 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____13617  in
                [uu____13616]
            | uu____13618 ->
                let uu____13619 =
                  let uu____13621 =
                    let uu____13622 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____13622  in
                  uu____13621 :: g  in
                let uu____13623 =
                  let uu____13625 =
                    let uu____13626 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____13626  in
                  [uu____13625]  in
                FStar_List.append uu____13619 uu____13623
             in
          (g1, env1)

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____13636 =
          let uu____13637 = FStar_Syntax_Subst.compress t  in
          uu____13637.FStar_Syntax_Syntax.n  in
        match uu____13636 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____13641)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____13644 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13647 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13650 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13652 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13654 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13662 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13665 =
            let uu____13666 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____13666 Prims.op_Negation  in
          if uu____13665
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13686 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Syntax_Const.effect_Tot_lid None
                                [FStar_Syntax_Syntax.TOTAL])))) None
                     tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____13706 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____13706 with
               | (aname,atok,env2) ->
                   let uu____13716 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____13716 with
                    | (formals,uu____13726) ->
                        let uu____13733 =
                          let uu____13736 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____13736 env2  in
                        (match uu____13733 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13744 =
                                 let uu____13745 =
                                   let uu____13751 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13759  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____13751,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____13745
                                  in
                               [uu____13744;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))]
                                in
                             let uu____13766 =
                               let aux uu____13795 uu____13796 =
                                 match (uu____13795, uu____13796) with
                                 | ((bv,uu____13823),(env3,acc_sorts,acc)) ->
                                     let uu____13844 = gen_term_var env3 bv
                                        in
                                     (match uu____13844 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____13766 with
                              | (uu____13882,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____13896 =
                                      let uu____13900 =
                                        let uu____13901 =
                                          let uu____13907 =
                                            let uu____13908 =
                                              let uu____13911 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____13911)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13908
                                             in
                                          ([[app]], xs_sorts, uu____13907)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13901
                                         in
                                      (uu____13900, (Some "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13896
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____13923 =
                                      let uu____13927 =
                                        let uu____13928 =
                                          let uu____13934 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____13934)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13928
                                         in
                                      (uu____13927,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13923
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____13944 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____13944 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13960,uu____13961)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13962 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____13962 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13973,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____13978 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13980  ->
                      match uu___118_13980 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13981 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13984 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13985 -> false))
               in
            Prims.op_Negation uu____13978  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None
                in
             let uu____13991 = encode_top_level_val env fv t quals  in
             match uu____13991 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____14003 =
                   let uu____14005 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____14005  in
                 (uu____14003, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____14010 = encode_formula f env  in
          (match uu____14010 with
           | (f1,decls) ->
               let g =
                 let uu____14019 =
                   let uu____14020 =
                     let uu____14024 =
                       let uu____14026 =
                         let uu____14027 = FStar_Syntax_Print.lid_to_string l
                            in
                         FStar_Util.format1 "Assumption: %s" uu____14027  in
                       Some uu____14026  in
                     let uu____14028 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str)
                        in
                     (f1, uu____14024, uu____14028)  in
                   FStar_SMTEncoding_Util.mkAssume uu____14020  in
                 [uu____14019]  in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____14032) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____14039 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____14046 =
                       let uu____14051 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____14051.FStar_Syntax_Syntax.fv_name  in
                     uu____14046.FStar_Syntax_Syntax.v  in
                   let uu____14055 =
                     let uu____14056 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____14056  in
                   if uu____14055
                   then
                     let val_decl =
                       let uu___151_14071 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___151_14071.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___151_14071.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___151_14071.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____14075 = encode_sigelt' env1 val_decl  in
                     match uu____14075 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs)
             in
          (match uu____14039 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____14092,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____14094;
                          FStar_Syntax_Syntax.lbtyp = uu____14095;
                          FStar_Syntax_Syntax.lbeff = uu____14096;
                          FStar_Syntax_Syntax.lbdef = uu____14097;_}::[]),uu____14098)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____14110 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____14110 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____14133 =
                   let uu____14135 =
                     let uu____14136 =
                       let uu____14140 =
                         let uu____14141 =
                           let uu____14147 =
                             let uu____14148 =
                               let uu____14151 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x])
                                  in
                               (valid_b2t_x, uu____14151)  in
                             FStar_SMTEncoding_Util.mkEq uu____14148  in
                           ([[b2t_x]], [xx], uu____14147)  in
                         FStar_SMTEncoding_Util.mkForall uu____14141  in
                       (uu____14140, (Some "b2t def"), "b2t_def")  in
                     FStar_SMTEncoding_Util.mkAssume uu____14136  in
                   [uu____14135]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____14133
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____14168,uu____14169) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_14173  ->
                  match uu___119_14173 with
                  | FStar_Syntax_Syntax.Discriminator uu____14174 -> true
                  | uu____14175 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____14177,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____14183 =
                     let uu____14184 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____14184.FStar_Ident.idText  in
                   uu____14183 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_14186  ->
                     match uu___120_14186 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____14187 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____14190) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_14198  ->
                  match uu___121_14198 with
                  | FStar_Syntax_Syntax.Projector uu____14199 -> true
                  | uu____14202 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____14209 = try_lookup_free_var env l  in
          (match uu____14209 with
           | Some uu____14213 -> ([], env)
           | None  ->
               let se1 =
                 let uu___152_14216 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___152_14216.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___152_14216.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___152_14216.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____14222) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____14232) ->
          let uu____14237 = encode_sigelts env ses  in
          (match uu____14237 with
           | (g,env1) ->
               let uu____14247 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_14257  ->
                         match uu___122_14257 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____14258;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____14259;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____14260;_}
                             -> false
                         | uu____14262 -> true))
                  in
               (match uu____14247 with
                | (g',inversions) ->
                    let uu____14271 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_14281  ->
                              match uu___123_14281 with
                              | FStar_SMTEncoding_Term.DeclFun uu____14282 ->
                                  true
                              | uu____14288 -> false))
                       in
                    (match uu____14271 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____14299,tps,k,uu____14302,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_14312  ->
                    match uu___124_14312 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____14313 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____14320 = c  in
              match uu____14320 with
              | (name,args,uu____14324,uu____14325,uu____14326) ->
                  let uu____14329 =
                    let uu____14330 =
                      let uu____14336 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____14343  ->
                                match uu____14343 with
                                | (uu____14347,sort,uu____14349) -> sort))
                         in
                      (name, uu____14336, FStar_SMTEncoding_Term.Term_sort,
                        None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____14330  in
                  [uu____14329]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____14367 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____14370 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____14370 FStar_Option.isNone))
               in
            if uu____14367
            then []
            else
              (let uu____14387 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____14387 with
               | (xxsym,xx) ->
                   let uu____14393 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____14404  ->
                             fun l  ->
                               match uu____14404 with
                               | (out,decls) ->
                                   let uu____14416 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____14416 with
                                    | (uu____14422,data_t) ->
                                        let uu____14424 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____14424 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____14453 =
                                                 let uu____14454 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____14454.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____14453 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____14462,indices) ->
                                                   indices
                                               | uu____14478 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14490  ->
                                                         match uu____14490
                                                         with
                                                         | (x,uu____14494) ->
                                                             let uu____14495
                                                               =
                                                               let uu____14496
                                                                 =
                                                                 let uu____14500
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____14500,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14496
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____14495)
                                                    env)
                                                in
                                             let uu____14502 =
                                               encode_args indices env1  in
                                             (match uu____14502 with
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
                                                      let uu____14526 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14534
                                                                 =
                                                                 let uu____14537
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____14537,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14534)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____14526
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____14539 =
                                                      let uu____14540 =
                                                        let uu____14543 =
                                                          let uu____14544 =
                                                            let uu____14547 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____14547,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14544
                                                           in
                                                        (out, uu____14543)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14540
                                                       in
                                                    (uu____14539,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____14393 with
                    | (data_ax,decls) ->
                        let uu____14555 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____14555 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14569 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14569 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____14572 =
                                 let uu____14576 =
                                   let uu____14577 =
                                     let uu____14583 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____14591 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____14583,
                                       uu____14591)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14577
                                    in
                                 let uu____14599 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____14576, (Some "inversion axiom"),
                                   uu____14599)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____14572
                                in
                             let pattern_guarded_inversion =
                               let uu____14603 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1"))
                                  in
                               if uu____14603
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                    in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp])
                                    in
                                 let uu____14614 =
                                   let uu____14615 =
                                     let uu____14619 =
                                       let uu____14620 =
                                         let uu____14626 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars)
                                            in
                                         let uu____14634 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax)
                                            in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14626, uu____14634)
                                          in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14620
                                        in
                                     let uu____14642 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str)
                                        in
                                     (uu____14619, (Some "inversion axiom"),
                                       uu____14642)
                                      in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14615
                                    in
                                 [uu____14614]
                               else []  in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion))))
             in
          let uu____14645 =
            let uu____14653 =
              let uu____14654 = FStar_Syntax_Subst.compress k  in
              uu____14654.FStar_Syntax_Syntax.n  in
            match uu____14653 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14683 -> (tps, k)  in
          (match uu____14645 with
           | (formals,res) ->
               let uu____14698 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____14698 with
                | (formals1,res1) ->
                    let uu____14705 = encode_binders None formals1 env  in
                    (match uu____14705 with
                     | (vars,guards,env',binder_decls,uu____14720) ->
                         let uu____14727 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____14727 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____14740 =
                                  let uu____14744 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____14744)  in
                                FStar_SMTEncoding_Util.mkApp uu____14740  in
                              let uu____14749 =
                                let tname_decl =
                                  let uu____14755 =
                                    let uu____14756 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14771  ->
                                              match uu____14771 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____14779 = varops.next_id ()  in
                                    (tname, uu____14756,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14779, false)
                                     in
                                  constructor_or_logic_type_decl uu____14755
                                   in
                                let uu____14784 =
                                  match vars with
                                  | [] ->
                                      let uu____14791 =
                                        let uu____14792 =
                                          let uu____14794 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_44  -> Some _0_44)
                                            uu____14794
                                           in
                                        push_free_var env1 t tname
                                          uu____14792
                                         in
                                      ([], uu____14791)
                                  | uu____14798 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____14804 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14804
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____14813 =
                                          let uu____14817 =
                                            let uu____14818 =
                                              let uu____14826 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats, None, vars, uu____14826)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14818
                                             in
                                          (uu____14817,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14813
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____14784 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____14749 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14849 =
                                       encode_term_pred None res1 env' tapp
                                        in
                                     match uu____14849 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14866 =
                                               let uu____14867 =
                                                 let uu____14871 =
                                                   let uu____14872 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14872
                                                    in
                                                 (uu____14871,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14867
                                                in
                                             [uu____14866]
                                           else []  in
                                         let uu____14875 =
                                           let uu____14877 =
                                             let uu____14879 =
                                               let uu____14880 =
                                                 let uu____14884 =
                                                   let uu____14885 =
                                                     let uu____14891 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____14891)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14885
                                                    in
                                                 (uu____14884, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14880
                                                in
                                             [uu____14879]  in
                                           FStar_List.append karr uu____14877
                                            in
                                         FStar_List.append decls1 uu____14875
                                      in
                                   let aux =
                                     let uu____14900 =
                                       let uu____14902 =
                                         inversion_axioms tapp vars  in
                                       let uu____14904 =
                                         let uu____14906 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____14906]  in
                                       FStar_List.append uu____14902
                                         uu____14904
                                        in
                                     FStar_List.append kindingAx uu____14900
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14911,uu____14912,uu____14913,uu____14914,uu____14915)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14920,t,uu____14922,n_tps,uu____14924) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____14929 = new_term_constant_and_tok_from_lid env d  in
          (match uu____14929 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____14940 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____14940 with
                | (formals,t_res) ->
                    let uu____14962 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____14962 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____14971 =
                           encode_binders (Some fuel_tm) formals env1  in
                         (match uu____14971 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____15009 =
                                            mk_term_projector_name d x  in
                                          (uu____15009,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____15011 =
                                  let uu____15021 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____15021, true)
                                   in
                                FStar_All.pipe_right uu____15011
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                 in
                              let app = mk_Apply ddtok_tm vars  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____15043 =
                                encode_term_pred None t env1 ddtok_tm  in
                              (match uu____15043 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____15051::uu____15052 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff
                                            in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff]  in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____15077 =
                                           let uu____15083 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____15083)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____15077
                                     | uu____15096 -> tok_typing  in
                                   let uu____15101 =
                                     encode_binders (Some fuel_tm) formals
                                       env1
                                      in
                                   (match uu____15101 with
                                    | (vars',guards',env'',decls_formals,uu____15116)
                                        ->
                                        let uu____15123 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1
                                           in
                                        (match uu____15123 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____15142 ->
                                                   let uu____15146 =
                                                     let uu____15147 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____15147
                                                      in
                                                   [uu____15146]
                                                in
                                             let encode_elim uu____15154 =
                                               let uu____15155 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____15155 with
                                               | (head1,args) ->
                                                   let uu____15184 =
                                                     let uu____15185 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____15185.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____15184 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____15192;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____15193;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____15194;_},uu____15195)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____15205 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____15205
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
                                                                 | uu____15231
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable"
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15239
                                                                    =
                                                                    let uu____15240
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15240
                                                                     in
                                                                    if
                                                                    uu____15239
                                                                    then
                                                                    let uu____15247
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15247]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____15249
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15262
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15262
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15284
                                                                    =
                                                                    let uu____15288
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15288
                                                                     in
                                                                    (match uu____15284
                                                                    with
                                                                    | 
                                                                    (uu____15295,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15301
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____15301
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15303
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15303
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 encoded_args
                                                                in
                                                             (match uu____15249
                                                              with
                                                              | (uu____15311,arg_vars,elim_eqns_or_guards,uu____15314)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____15333
                                                                    =
                                                                    let uu____15337
                                                                    =
                                                                    let uu____15338
                                                                    =
                                                                    let uu____15344
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15350
                                                                    =
                                                                    let uu____15351
                                                                    =
                                                                    let uu____15354
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15354)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15351
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15344,
                                                                    uu____15350)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15338
                                                                     in
                                                                    (uu____15337,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15333
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15367
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____15367,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15369
                                                                    =
                                                                    let uu____15373
                                                                    =
                                                                    let uu____15374
                                                                    =
                                                                    let uu____15380
                                                                    =
                                                                    let uu____15383
                                                                    =
                                                                    let uu____15385
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15385]
                                                                     in
                                                                    [uu____15383]
                                                                     in
                                                                    let uu____15388
                                                                    =
                                                                    let uu____15389
                                                                    =
                                                                    let uu____15392
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15393
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15392,
                                                                    uu____15393)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15389
                                                                     in
                                                                    (uu____15380,
                                                                    [x],
                                                                    uu____15388)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15374
                                                                     in
                                                                    let uu____15403
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15373,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15403)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15369
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15408
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
                                                                    (let uu____15423
                                                                    =
                                                                    let uu____15424
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15424
                                                                    dapp1  in
                                                                    [uu____15423])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15408
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15428
                                                                    =
                                                                    let uu____15432
                                                                    =
                                                                    let uu____15433
                                                                    =
                                                                    let uu____15439
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15445
                                                                    =
                                                                    let uu____15446
                                                                    =
                                                                    let uu____15449
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15449)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15446
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15439,
                                                                    uu____15445)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15433
                                                                     in
                                                                    (uu____15432,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15428)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____15465 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____15465
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
                                                                 | uu____15491
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable"
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15499
                                                                    =
                                                                    let uu____15500
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15500
                                                                     in
                                                                    if
                                                                    uu____15499
                                                                    then
                                                                    let uu____15507
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____15507]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____15509
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15522
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15522
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15544
                                                                    =
                                                                    let uu____15548
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15548
                                                                     in
                                                                    (match uu____15544
                                                                    with
                                                                    | 
                                                                    (uu____15555,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15561
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv
                                                                     in
                                                                    uu____15561
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15563
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____15563
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 encoded_args
                                                                in
                                                             (match uu____15509
                                                              with
                                                              | (uu____15571,arg_vars,elim_eqns_or_guards,uu____15574)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____15593
                                                                    =
                                                                    let uu____15597
                                                                    =
                                                                    let uu____15598
                                                                    =
                                                                    let uu____15604
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15610
                                                                    =
                                                                    let uu____15611
                                                                    =
                                                                    let uu____15614
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____15614)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15611
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15604,
                                                                    uu____15610)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15598
                                                                     in
                                                                    (uu____15597,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15593
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15627
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____15627,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____15629
                                                                    =
                                                                    let uu____15633
                                                                    =
                                                                    let uu____15634
                                                                    =
                                                                    let uu____15640
                                                                    =
                                                                    let uu____15643
                                                                    =
                                                                    let uu____15645
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____15645]
                                                                     in
                                                                    [uu____15643]
                                                                     in
                                                                    let uu____15648
                                                                    =
                                                                    let uu____15649
                                                                    =
                                                                    let uu____15652
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____15653
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____15652,
                                                                    uu____15653)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15649
                                                                     in
                                                                    (uu____15640,
                                                                    [x],
                                                                    uu____15648)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15634
                                                                     in
                                                                    let uu____15663
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____15633,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15663)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15629
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15668
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
                                                                    (let uu____15683
                                                                    =
                                                                    let uu____15684
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15684
                                                                    dapp1  in
                                                                    [uu____15683])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____15668
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____15688
                                                                    =
                                                                    let uu____15692
                                                                    =
                                                                    let uu____15693
                                                                    =
                                                                    let uu____15699
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____15705
                                                                    =
                                                                    let uu____15706
                                                                    =
                                                                    let uu____15709
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____15709)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15706
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15699,
                                                                    uu____15705)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15693
                                                                     in
                                                                    (uu____15692,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15688)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15719 ->
                                                        ((let uu____15721 =
                                                            let uu____15722 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____15723 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15722
                                                              uu____15723
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15721);
                                                         ([], [])))
                                                in
                                             let uu____15726 = encode_elim ()
                                                in
                                             (match uu____15726 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15738 =
                                                      let uu____15740 =
                                                        let uu____15742 =
                                                          let uu____15744 =
                                                            let uu____15746 =
                                                              let uu____15747
                                                                =
                                                                let uu____15753
                                                                  =
                                                                  let uu____15755
                                                                    =
                                                                    let uu____15756
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15756
                                                                     in
                                                                  Some
                                                                    uu____15755
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15753)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15747
                                                               in
                                                            [uu____15746]  in
                                                          let uu____15759 =
                                                            let uu____15761 =
                                                              let uu____15763
                                                                =
                                                                let uu____15765
                                                                  =
                                                                  let uu____15767
                                                                    =
                                                                    let uu____15769
                                                                    =
                                                                    let uu____15771
                                                                    =
                                                                    let uu____15772
                                                                    =
                                                                    let uu____15776
                                                                    =
                                                                    let uu____15777
                                                                    =
                                                                    let uu____15783
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15783)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15777
                                                                     in
                                                                    (uu____15776,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15772
                                                                     in
                                                                    let uu____15790
                                                                    =
                                                                    let uu____15792
                                                                    =
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
                                                                    vars'  in
                                                                    let uu____15810
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15804,
                                                                    uu____15810)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15798
                                                                     in
                                                                    (uu____15797,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15793
                                                                     in
                                                                    [uu____15792]
                                                                     in
                                                                    uu____15771
                                                                    ::
                                                                    uu____15790
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15769
                                                                     in
                                                                  FStar_List.append
                                                                    uu____15767
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15765
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15763
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15761
                                                             in
                                                          FStar_List.append
                                                            uu____15744
                                                            uu____15759
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____15742
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____15740
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15738
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15831  ->
              fun se  ->
                match uu____15831 with
                | (g,env1) ->
                    let uu____15843 = encode_sigelt env1 se  in
                    (match uu____15843 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t * env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15881 =
        match uu____15881 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15899 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____15904 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____15904
                   then
                     let uu____15905 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____15906 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____15907 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15905 uu____15906 uu____15907
                   else ());
                  (let uu____15909 = encode_term t1 env1  in
                   match uu____15909 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____15919 =
                         let uu____15923 =
                           let uu____15924 =
                             let uu____15925 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____15925
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____15924  in
                         new_term_constant_from_string env1 x uu____15923  in
                       (match uu____15919 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t
                               in
                            let caption =
                              let uu____15936 = FStar_Options.log_queries ()
                                 in
                              if uu____15936
                              then
                                let uu____15938 =
                                  let uu____15939 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____15940 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____15941 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15939 uu____15940 uu____15941
                                   in
                                Some uu____15938
                              else None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (Some a_name), a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15952,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None
                    in
                 let uu____15961 = encode_free_var env1 fv t t_norm []  in
                 (match uu____15961 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15974,se,uu____15976) ->
                 let uu____15979 = encode_sigelt env1 se  in
                 (match uu____15979 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15989,se) ->
                 let uu____15993 = encode_sigelt env1 se  in
                 (match uu____15993 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____16003 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____16003 with | (uu____16015,decls,env1) -> (decls, env1)
  
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____16063  ->
            match uu____16063 with
            | (l,uu____16070,uu____16071) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None)))
     in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____16092  ->
            match uu____16092 with
            | (l,uu____16100,uu____16101) ->
                let uu____16106 =
                  FStar_All.pipe_left
                    (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45) (
                    fst l)
                   in
                let uu____16107 =
                  let uu____16109 =
                    let uu____16110 = FStar_SMTEncoding_Util.mkFreeV l  in
                    FStar_SMTEncoding_Term.Eval uu____16110  in
                  [uu____16109]  in
                uu____16106 :: uu____16107))
     in
  (prefix1, suffix) 
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____16122 =
      let uu____16124 =
        let uu____16125 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____16127 =
          let uu____16128 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____16128 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____16125;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____16127
        }  in
      [uu____16124]  in
    FStar_ST.write last_env uu____16122
  
let get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____16140 = FStar_ST.read last_env  in
      match uu____16140 with
      | [] -> failwith "No env; call init first!"
      | e::uu____16146 ->
          let uu___153_16148 = e  in
          let uu____16149 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___153_16148.bindings);
            depth = (uu___153_16148.depth);
            tcenv;
            warn = (uu___153_16148.warn);
            cache = (uu___153_16148.cache);
            nolabels = (uu___153_16148.nolabels);
            use_zfuel_name = (uu___153_16148.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___153_16148.encode_non_total_function_typ);
            current_module_name = uu____16149
          }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____16154 = FStar_ST.read last_env  in
    match uu____16154 with
    | [] -> failwith "Empty env stack"
    | uu____16159::tl1 -> FStar_ST.write last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____16168  ->
    let uu____16169 = FStar_ST.read last_env  in
    match uu____16169 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___154_16180 = hd1  in
          {
            bindings = (uu___154_16180.bindings);
            depth = (uu___154_16180.depth);
            tcenv = (uu___154_16180.tcenv);
            warn = (uu___154_16180.warn);
            cache = refs;
            nolabels = (uu___154_16180.nolabels);
            use_zfuel_name = (uu___154_16180.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_16180.encode_non_total_function_typ);
            current_module_name = (uu___154_16180.current_module_name)
          }  in
        FStar_ST.write last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____16187  ->
    let uu____16188 = FStar_ST.read last_env  in
    match uu____16188 with
    | [] -> failwith "Popping an empty stack"
    | uu____16193::tl1 -> FStar_ST.write last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____16202  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____16206  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____16210  ->
    let uu____16211 = FStar_ST.read last_env  in
    match uu____16211 with
    | hd1::uu____16217::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____16223 -> failwith "Impossible"
  
let init : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let push : Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let pop : Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg 
let mark : Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg 
let reset_mark : Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
  
let commit_mark : Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
  
let open_fact_db_tags : env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> [] 
let place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____16282::uu____16283,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___155_16287 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___155_16287.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___155_16287.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___155_16287.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____16288 -> d
  
let fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____16301 =
        let uu____16303 =
          let uu____16304 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____16304  in
        let uu____16305 = open_fact_db_tags env  in uu____16303 ::
          uu____16305
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____16301
  
let encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list * env_t)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____16322 = encode_sigelt env se  in
      match uu____16322 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____16349 = FStar_Options.log_queries ()  in
        if uu____16349
        then
          let uu____16351 =
            let uu____16352 =
              let uu____16353 =
                let uu____16354 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____16354 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____16353  in
            FStar_SMTEncoding_Term.Caption uu____16352  in
          uu____16351 :: decls
        else decls  in
      let env =
        let uu____16361 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____16361 tcenv  in
      let uu____16362 = encode_top_level_facts env se  in
      match uu____16362 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____16371 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____16371))
  
let encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____16384 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____16384
       then
         let uu____16385 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____16385
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____16408  ->
                 fun se  ->
                   match uu____16408 with
                   | (g,env2) ->
                       let uu____16420 = encode_top_level_facts env2 se  in
                       (match uu____16420 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____16433 =
         encode_signature
           (let uu___156_16437 = env  in
            {
              bindings = (uu___156_16437.bindings);
              depth = (uu___156_16437.depth);
              tcenv = (uu___156_16437.tcenv);
              warn = false;
              cache = (uu___156_16437.cache);
              nolabels = (uu___156_16437.nolabels);
              use_zfuel_name = (uu___156_16437.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___156_16437.encode_non_total_function_typ);
              current_module_name = (uu___156_16437.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____16433 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____16449 = FStar_Options.log_queries ()  in
             if uu____16449
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___157_16454 = env1  in
               {
                 bindings = (uu___157_16454.bindings);
                 depth = (uu___157_16454.depth);
                 tcenv = (uu___157_16454.tcenv);
                 warn = true;
                 cache = (uu___157_16454.cache);
                 nolabels = (uu___157_16454.nolabels);
                 use_zfuel_name = (uu___157_16454.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___157_16454.encode_non_total_function_typ);
                 current_module_name = (uu___157_16454.current_module_name)
               });
            (let uu____16456 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____16456
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let encode_query :
  (Prims.unit -> Prims.string) option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list *
          FStar_SMTEncoding_ErrorReporting.label Prims.list *
          FStar_SMTEncoding_Term.decl * FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____16494 =
           let uu____16495 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____16495.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____16494);
        (let env =
           let uu____16497 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____16497 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____16504 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____16525 = aux rest  in
                 (match uu____16525 with
                  | (out,rest1) ->
                      let t =
                        let uu____16543 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____16543 with
                        | Some uu____16547 ->
                            let uu____16548 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit
                               in
                            FStar_Syntax_Util.refine uu____16548
                              x.FStar_Syntax_Syntax.sort
                        | uu____16549 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____16552 =
                        let uu____16554 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___158_16555 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___158_16555.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___158_16555.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____16554 :: out  in
                      (uu____16552, rest1))
             | uu____16558 -> ([], bindings1)  in
           let uu____16562 = aux bindings  in
           match uu____16562 with
           | (closing,bindings1) ->
               let uu____16576 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____16576, bindings1)
            in
         match uu____16504 with
         | (q1,bindings1) ->
             let uu____16589 =
               let uu____16592 =
                 FStar_List.filter
                   (fun uu___125_16594  ->
                      match uu___125_16594 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16595 ->
                          false
                      | uu____16599 -> true) bindings1
                  in
               encode_env_bindings env uu____16592  in
             (match uu____16589 with
              | (env_decls,env1) ->
                  ((let uu____16610 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____16610
                    then
                      let uu____16611 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16611
                    else ());
                   (let uu____16613 = encode_formula q1 env1  in
                    match uu____16613 with
                    | (phi,qdecls) ->
                        let uu____16625 =
                          let uu____16628 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16628 phi
                           in
                        (match uu____16625 with
                         | (labels,phi1) ->
                             let uu____16638 = encode_labels labels  in
                             (match uu____16638 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____16659 =
                                      let uu____16663 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____16664 =
                                        varops.mk_unique "@query"  in
                                      (uu____16663, (Some "query"),
                                        uu____16664)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16659
                                     in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"]
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16679 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____16679 tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16681 = encode_formula q env  in
       match uu____16681 with
       | (f,uu____16685) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16687) -> true
             | uu____16690 -> false)))
  