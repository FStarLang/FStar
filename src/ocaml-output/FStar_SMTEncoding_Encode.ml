open Prims
let add_fuel :
  'Auu____7 . 'Auu____7 -> 'Auu____7 Prims.list -> 'Auu____7 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____22 = FStar_Options.unthrottle_inductives ()  in
      if uu____22 then tl1 else x :: tl1
  
let withenv :
  'Auu____36 'Auu____37 'Auu____38 .
    'Auu____38 ->
      ('Auu____37,'Auu____36) FStar_Pervasives_Native.tuple2 ->
        ('Auu____37,'Auu____36,'Auu____38) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____56  -> match uu____56 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____71 'Auu____72 'Auu____73 .
    (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____73,'Auu____72) FStar_Util.either,'Auu____71)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___106_119  ->
         match uu___106_119 with
         | (FStar_Util.Inl uu____128,uu____129) -> false
         | uu____134 -> true) args
  
let subst_lcomp_opt :
  'Auu____149 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
        FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,'Auu____149) FStar_Util.either
          FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
          let uu____185 =
            let uu____190 =
              let uu____191 =
                let uu____194 = l1.FStar_Syntax_Syntax.comp ()  in
                FStar_Syntax_Subst.subst_comp s uu____194  in
              FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____191
               in
            FStar_Util.Inl uu____190  in
          FStar_Pervasives_Native.Some uu____185
      | uu____201 -> l
  
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_' 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___130_221 = a  in
        let uu____222 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____222;
          FStar_Syntax_Syntax.index =
            (uu___130_221.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___130_221.FStar_Syntax_Syntax.sort)
        }  in
      let uu____223 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____223
  
let primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____239 =
          let uu____240 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____240  in
        let uu____241 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____241 with
        | (uu____246,t) ->
            let uu____248 =
              let uu____249 = FStar_Syntax_Subst.compress t  in
              uu____249.FStar_Syntax_Syntax.n  in
            (match uu____248 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____270 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____270 with
                  | (binders,uu____276) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____291 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____300 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____300
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____309 =
        let uu____314 = mk_term_projector_name lid a  in
        (uu____314,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____309
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____323 =
        let uu____328 = mk_term_projector_name_by_pos lid i  in
        (uu____328,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____323
  
let mk_data_tester :
  'Auu____337 .
    'Auu____337 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
  
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
  let new_scope uu____946 =
    let uu____947 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____950 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____947, uu____950)  in
  let scopes =
    let uu____970 = let uu____981 = new_scope ()  in [uu____981]  in
    FStar_Util.mk_ref uu____970  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1022 =
        let uu____1025 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1025
          (fun uu____1111  ->
             match uu____1111 with
             | (names1,uu____1123) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1022 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1132 ->
          (FStar_Util.incr ctr;
           (let uu____1155 =
              let uu____1156 =
                let uu____1157 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1157  in
              Prims.strcat "__" uu____1156  in
            Prims.strcat y1 uu____1155))
       in
    let top_scope =
      let uu____1185 =
        let uu____1194 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1194
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1185  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1306 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1357 =
      let uu____1358 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1358  in
    FStar_Util.format2 "%s_%s" pfx uu____1357  in
  let string_const s =
    let uu____1363 =
      let uu____1366 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1366
        (fun uu____1452  ->
           match uu____1452 with
           | (uu____1463,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1363 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 ()  in
        let f =
          let uu____1476 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1476  in
        let top_scope =
          let uu____1480 =
            let uu____1489 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1489  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1480  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1590 =
    let uu____1591 =
      let uu____1602 = new_scope ()  in
      let uu____1611 = FStar_ST.op_Bang scopes  in uu____1602 :: uu____1611
       in
    FStar_ST.op_Colon_Equals scopes uu____1591  in
  let pop1 uu____1761 =
    let uu____1762 =
      let uu____1773 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1773
       in
    FStar_ST.op_Colon_Equals scopes uu____1762  in
  let mark1 uu____1923 = push1 ()  in
  let reset_mark1 uu____1927 = pop1 ()  in
  let commit_mark1 uu____1931 =
    let uu____1932 = FStar_ST.op_Bang scopes  in
    match uu____1932 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.op_Colon_Equals scopes ((next1, next2) :: tl1))
    | uu____2144 -> failwith "Impossible"  in
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
    let uu___131_2159 = x  in
    let uu____2160 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____2160;
      FStar_Syntax_Syntax.index = (uu___131_2159.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___131_2159.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2 
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4 
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____2194 -> false
  
let __proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____2232 -> false
  
let __proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____2283 'Auu____2284 .
    'Auu____2284 ->
      ('Auu____2284,'Auu____2283 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
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
  
let mk_cache_entry :
  'Auu____2598 .
    'Auu____2598 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls  ->
          let names1 =
            FStar_All.pipe_right t_decls
              (FStar_List.collect
                 (fun uu___107_2632  ->
                    match uu___107_2632 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2636 -> []))
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
    let uu____2647 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___108_2657  ->
              match uu___108_2657 with
              | Binding_var (x,uu____2659) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2661,uu____2662,uu____2663) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____2647 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2680 .
    env_t ->
      (binding -> 'Auu____2680 FStar_Pervasives_Native.option) ->
        'Auu____2680 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2710 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2710
      then
        let uu____2713 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2713
      else FStar_Pervasives_Native.None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____2728 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2728)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___132_2746 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___132_2746.tcenv);
           warn = (uu___132_2746.warn);
           cache = (uu___132_2746.cache);
           nolabels = (uu___132_2746.nolabels);
           use_zfuel_name = (uu___132_2746.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___132_2746.encode_non_total_function_typ);
           current_module_name = (uu___132_2746.current_module_name)
         }))
  
let new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      (ysym, y,
        (let uu___133_2766 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___133_2766.depth);
           tcenv = (uu___133_2766.tcenv);
           warn = (uu___133_2766.warn);
           cache = (uu___133_2766.cache);
           nolabels = (uu___133_2766.nolabels);
           use_zfuel_name = (uu___133_2766.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___133_2766.encode_non_total_function_typ);
           current_module_name = (uu___133_2766.current_module_name)
         }))
  
let new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        (ysym, y,
          (let uu___134_2790 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___134_2790.depth);
             tcenv = (uu___134_2790.tcenv);
             warn = (uu___134_2790.warn);
             cache = (uu___134_2790.cache);
             nolabels = (uu___134_2790.nolabels);
             use_zfuel_name = (uu___134_2790.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___134_2790.encode_non_total_function_typ);
             current_module_name = (uu___134_2790.current_module_name)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___135_2803 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___135_2803.depth);
          tcenv = (uu___135_2803.tcenv);
          warn = (uu___135_2803.warn);
          cache = (uu___135_2803.cache);
          nolabels = (uu___135_2803.nolabels);
          use_zfuel_name = (uu___135_2803.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___135_2803.encode_non_total_function_typ);
          current_module_name = (uu___135_2803.current_module_name)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___109_2829  ->
             match uu___109_2829 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2842 -> FStar_Pervasives_Native.None)
         in
      let uu____2847 = aux a  in
      match uu____2847 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2859 = aux a2  in
          (match uu____2859 with
           | FStar_Pervasives_Native.None  ->
               let uu____2870 =
                 let uu____2871 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2872 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2871 uu____2872
                  in
               failwith uu____2870
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____2901 =
        let uu___136_2902 = env  in
        let uu____2903 =
          let uu____2906 =
            let uu____2907 =
              let uu____2920 =
                let uu____2923 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left
                  (fun _0_41  -> FStar_Pervasives_Native.Some _0_41)
                  uu____2923
                 in
              (x, fname, uu____2920, FStar_Pervasives_Native.None)  in
            Binding_fvar uu____2907  in
          uu____2906 :: (env.bindings)  in
        {
          bindings = uu____2903;
          depth = (uu___136_2902.depth);
          tcenv = (uu___136_2902.tcenv);
          warn = (uu___136_2902.warn);
          cache = (uu___136_2902.cache);
          nolabels = (uu___136_2902.nolabels);
          use_zfuel_name = (uu___136_2902.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___136_2902.encode_non_total_function_typ);
          current_module_name = (uu___136_2902.current_module_name)
        }  in
      (fname, ftok, uu____2901)
  
let try_lookup_lid :
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
        (fun uu___110_2967  ->
           match uu___110_2967 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____3006 -> FStar_Pervasives_Native.None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____3025 =
        lookup_binding env
          (fun uu___111_3033  ->
             match uu___111_3033 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____3048 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____3025 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____3069 = try_lookup_lid env a  in
      match uu____3069 with
      | FStar_Pervasives_Native.None  ->
          let uu____3102 =
            let uu____3103 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____3103  in
          failwith uu____3102
      | FStar_Pervasives_Native.Some s -> s
  
let push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___137_3155 = env  in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___137_3155.depth);
            tcenv = (uu___137_3155.tcenv);
            warn = (uu___137_3155.warn);
            cache = (uu___137_3155.cache);
            nolabels = (uu___137_3155.nolabels);
            use_zfuel_name = (uu___137_3155.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___137_3155.encode_non_total_function_typ);
            current_module_name = (uu___137_3155.current_module_name)
          }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____3172 = lookup_lid env x  in
        match uu____3172 with
        | (t1,t2,uu____3185) ->
            let t3 =
              let uu____3195 =
                let uu____3202 =
                  let uu____3205 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____3205]  in
                (f, uu____3202)  in
              FStar_SMTEncoding_Util.mkApp uu____3195  in
            let uu___138_3210 = env  in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___138_3210.depth);
              tcenv = (uu___138_3210.tcenv);
              warn = (uu___138_3210.warn);
              cache = (uu___138_3210.cache);
              nolabels = (uu___138_3210.nolabels);
              use_zfuel_name = (uu___138_3210.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___138_3210.encode_non_total_function_typ);
              current_module_name = (uu___138_3210.current_module_name)
            }
  
let try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____3225 = try_lookup_lid env l  in
      match uu____3225 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3274 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3282,fuel::[]) ->
                         let uu____3286 =
                           let uu____3287 =
                             let uu____3288 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____3288
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____3287 "fuel"  in
                         if uu____3286
                         then
                           let uu____3291 =
                             let uu____3292 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3292
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_42  ->
                                FStar_Pervasives_Native.Some _0_42)
                             uu____3291
                         else FStar_Pervasives_Native.Some t
                     | uu____3296 -> FStar_Pervasives_Native.Some t)
                | uu____3297 -> FStar_Pervasives_Native.None))
  
let lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____3312 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____3312 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3316 =
            let uu____3317 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____3317  in
          failwith uu____3316
  
let lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____3330 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____3330 with | (x,uu____3342,uu____3343) -> x
  
let lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3370 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____3370 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3406;
                 FStar_SMTEncoding_Term.rng = uu____3407;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3422 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3446 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___112_3464  ->
           match uu___112_3464 with
           | Binding_fvar (uu____3467,nm',tok,uu____3470) when nm = nm' ->
               tok
           | uu____3479 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____3486 .
    'Auu____3486 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3504  ->
      match uu____3504 with
      | (pats,vars,body) ->
          let fallback uu____3529 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____3534 = FStar_Options.unthrottle_inductives ()  in
          if uu____3534
          then fallback ()
          else
            (let uu____3536 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____3536 with
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
                           | uu____3567 -> p))
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
                             let uu____3588 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____3588
                         | uu____3591 ->
                             let uu____3592 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____3592 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3597 -> body  in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                    in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1") 
let head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3641 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3654 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3661 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3662 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3679 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3696 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3698 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3698 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3716;
             FStar_Syntax_Syntax.vars = uu____3717;_},uu____3718)
          ->
          let uu____3739 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3739 FStar_Option.isNone
      | uu____3756 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3765 =
        let uu____3766 = FStar_Syntax_Util.un_uinst t  in
        uu____3766.FStar_Syntax_Syntax.n  in
      match uu____3765 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3769,uu____3770,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___113_3791  ->
                  match uu___113_3791 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3792 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3794 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3794 FStar_Option.isSome
      | uu____3811 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3820 = head_normal env t  in
      if uu____3820
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
    let uu____3834 =
      let uu____3835 = FStar_Syntax_Syntax.null_binder t  in [uu____3835]  in
    let uu____3836 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3834 uu____3836 FStar_Pervasives_Native.None
  
let mk_Apply :
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
                    let uu____3876 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3876
                | s ->
                    let uu____3881 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3881) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___114_3899  ->
    match uu___114_3899 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3900 -> false
  
let is_an_eta_expansion :
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
                       FStar_SMTEncoding_Term.freevars = uu____3939;
                       FStar_SMTEncoding_Term.rng = uu____3940;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3963) ->
              let uu____3972 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3983 -> false) args (FStar_List.rev xs))
                 in
              if uu____3972
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3987,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3991 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3995 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3995))
                 in
              if uu____3991
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3999 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }
let __proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let __proj__Mkpattern__item__pat_term :
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
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
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
    | uu____4229 -> false
  
let encode_const : FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___115_4233  ->
    match uu___115_4233 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____4235 =
          let uu____4242 =
            let uu____4245 =
              let uu____4246 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c)
                 in
              FStar_SMTEncoding_Term.boxInt uu____4246  in
            [uu____4245]  in
          ("FStar.Char.Char", uu____4242)  in
        FStar_SMTEncoding_Util.mkApp uu____4235
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____4260 = FStar_SMTEncoding_Util.mkInteger i  in
        FStar_SMTEncoding_Term.boxInt uu____4260
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____4262) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____4278) ->
        let uu____4283 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes
           in
        varops.string_const uu____4283
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____4288 =
          let uu____4289 = FStar_Syntax_Print.const_to_string c  in
          FStar_Util.format1 "Unhandled constant: %s" uu____4289  in
        failwith uu____4288
  
let as_function_typ :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____4310 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____4323 ->
            let uu____4330 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____4330
        | uu____4331 ->
            if norm1
            then let uu____4332 = whnf env t1  in aux false uu____4332
            else
              (let uu____4334 =
                 let uu____4335 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____4336 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____4335 uu____4336
                  in
               failwith uu____4334)
         in
      aux true t0
  
let curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____4368 ->
        let uu____4369 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____4369)
  
let is_arithmetic_primitive :
  'Auu____4386 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____4386 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4406::uu____4407::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____4411::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____4414 -> false
  
let isInteger : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____4436 -> false
  
let getInteger : FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4452 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4459 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4459)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4498)::uu____4499::uu____4500::[]) ->
          (((((((((FStar_Syntax_Syntax.fv_eq_lid fv
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
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4551)::uu____4552::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4589 -> false
  
let rec encode_binders :
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
        (let uu____4798 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4798
         then
           let uu____4799 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4799
         else ());
        (let uu____4801 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4885  ->
                   fun b  ->
                     match uu____4885 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4964 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4980 = gen_term_var env1 x  in
                           match uu____4980 with
                           | (xxsym,xx,env') ->
                               let uu____5004 =
                                 let uu____5009 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____5009 env1 xx
                                  in
                               (match uu____5004 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4964 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4801 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and encode_term_pred :
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
          let uu____5168 = encode_term t env  in
          match uu____5168 with
          | (t1,decls) ->
              let uu____5179 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____5179, decls)

and encode_term_pred' :
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
          let uu____5190 = encode_term t env  in
          match uu____5190 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____5205 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____5205, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____5207 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____5207, decls))

and encode_arith_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5213 = encode_args args_e env  in
        match uu____5213 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____5232 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____5241 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____5241  in
            let binary arg_tms1 =
              let uu____5254 =
                let uu____5255 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____5255  in
              let uu____5256 =
                let uu____5257 =
                  let uu____5258 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____5258  in
                FStar_SMTEncoding_Term.unboxInt uu____5257  in
              (uu____5254, uu____5256)  in
            let mk_default uu____5264 =
              let uu____5265 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____5265 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms))
               in
            let mk_l op mk_args ts =
              let uu____5316 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____5316
              then
                let uu____5317 =
                  let uu____5318 = mk_args ts  in op uu____5318  in
                FStar_All.pipe_right uu____5317 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5347 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5347
              then
                let uu____5348 = binary ts  in
                match uu____5348 with
                | (t1,t2) ->
                    let uu____5355 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5355
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5359 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5359
                 then
                   let uu____5360 = op (binary ts)  in
                   FStar_All.pipe_right uu____5360
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
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____5491 =
              let uu____5500 =
                FStar_List.tryFind
                  (fun uu____5522  ->
                     match uu____5522 with
                     | (l,uu____5532) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5500 FStar_Util.must  in
            (match uu____5491 with
             | (uu____5571,op) ->
                 let uu____5581 = op arg_tms  in (uu____5581, decls))

and encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5589 = FStar_List.hd args_e  in
        match uu____5589 with
        | (tm_sz,uu____5597) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5607 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5607 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
                  ((let uu____5615 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5615);
                   t_decls)
               in
            let uu____5616 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5636::(sz_arg,uu____5638)::uu____5639::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5688 =
                    let uu____5691 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5691  in
                  let uu____5694 =
                    let uu____5697 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5697  in
                  (uu____5688, uu____5694)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5703::(sz_arg,uu____5705)::uu____5706::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5755 =
                    let uu____5756 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5756
                     in
                  failwith uu____5755
              | uu____5765 ->
                  let uu____5772 = FStar_List.tail args_e  in
                  (uu____5772, FStar_Pervasives_Native.None)
               in
            (match uu____5616 with
             | (arg_tms,ext_sz) ->
                 let uu____5795 = encode_args arg_tms env  in
                 (match uu____5795 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5816 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5825 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5825  in
                      let unary_arith arg_tms2 =
                        let uu____5834 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5834  in
                      let binary arg_tms2 =
                        let uu____5847 =
                          let uu____5848 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5848
                           in
                        let uu____5849 =
                          let uu____5850 =
                            let uu____5851 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5851  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5850
                           in
                        (uu____5847, uu____5849)  in
                      let binary_arith arg_tms2 =
                        let uu____5866 =
                          let uu____5867 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5867
                           in
                        let uu____5868 =
                          let uu____5869 =
                            let uu____5870 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5870  in
                          FStar_SMTEncoding_Term.unboxInt uu____5869  in
                        (uu____5866, uu____5868)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____5919 =
                          let uu____5920 = mk_args ts  in op uu____5920  in
                        FStar_All.pipe_right uu____5919 resBox  in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____6028 =
                          let uu____6031 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____6031  in
                        let uu____6033 =
                          let uu____6036 =
                            let uu____6037 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____6037  in
                          FStar_SMTEncoding_Term.boxBitVec uu____6036  in
                        mk_bv uu____6028 unary uu____6033 arg_tms2  in
                      let to_int =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
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
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____6212 =
                        let uu____6221 =
                          FStar_List.tryFind
                            (fun uu____6243  ->
                               match uu____6243 with
                               | (l,uu____6253) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____6221 FStar_Util.must  in
                      (match uu____6212 with
                       | (uu____6294,op) ->
                           let uu____6304 = op arg_tms1  in
                           (uu____6304, (FStar_List.append sz_decls decls)))))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____6315 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____6315
       then
         let uu____6316 = FStar_Syntax_Print.tag_of_term t  in
         let uu____6317 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____6318 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____6316 uu____6317
           uu____6318
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6324 ->
           let uu____6349 =
             let uu____6350 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6351 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6352 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6353 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6350
               uu____6351 uu____6352 uu____6353
              in
           failwith uu____6349
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6358 =
             let uu____6359 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6360 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6361 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6362 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6359
               uu____6360 uu____6361 uu____6362
              in
           failwith uu____6358
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6368 =
             let uu____6369 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6369
              in
           failwith uu____6368
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6376) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6418) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6428 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6428, [])
       | FStar_Syntax_Syntax.Tm_type uu____6431 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6435) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____6441 = encode_const c  in (uu____6441, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6463 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6463 with
            | (binders1,res) ->
                let uu____6474 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6474
                then
                  let uu____6479 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6479 with
                   | (vars,guards,env',decls,uu____6504) ->
                       let fsym =
                         let uu____6522 = varops.fresh "f"  in
                         (uu____6522, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6525 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___139_6534 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___139_6534.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___139_6534.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___139_6534.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___139_6534.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___139_6534.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___139_6534.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___139_6534.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___139_6534.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___139_6534.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___139_6534.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___139_6534.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___139_6534.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___139_6534.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___139_6534.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___139_6534.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___139_6534.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___139_6534.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___139_6534.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___139_6534.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___139_6534.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.type_of =
                                (uu___139_6534.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___139_6534.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___139_6534.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___139_6534.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___139_6534.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___139_6534.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___139_6534.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___139_6534.FStar_TypeChecker_Env.identifier_info)
                            }) res
                          in
                       (match uu____6525 with
                        | (pre_opt,res_t) ->
                            let uu____6545 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6545 with
                             | (res_pred,decls') ->
                                 let uu____6556 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6569 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6569, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6573 =
                                         encode_formula pre env'  in
                                       (match uu____6573 with
                                        | (guard,decls0) ->
                                            let uu____6586 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6586, decls0))
                                    in
                                 (match uu____6556 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6598 =
                                          let uu____6609 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6609)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6598
                                         in
                                      let cvars =
                                        let uu____6627 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6627
                                          (FStar_List.filter
                                             (fun uu____6641  ->
                                                match uu____6641 with
                                                | (x,uu____6647) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____6666 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6666 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6674 =
                                             let uu____6675 =
                                               let uu____6682 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6682)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6675
                                              in
                                           (uu____6674,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6702 =
                                               let uu____6703 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6703
                                                in
                                             varops.mk_unique uu____6702  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____6714 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____6714
                                             then
                                               let uu____6717 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6717
                                             else
                                               FStar_Pervasives_Native.None
                                              in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____6725 =
                                               let uu____6732 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6732)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6725
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
                                             let uu____6744 =
                                               let uu____6751 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6751,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6744
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
                                             let uu____6772 =
                                               let uu____6779 =
                                                 let uu____6780 =
                                                   let uu____6791 =
                                                     let uu____6792 =
                                                       let uu____6797 =
                                                         let uu____6798 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6798
                                                          in
                                                       (f_has_t, uu____6797)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6792
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6791)
                                                    in
                                                 mkForall_fuel uu____6780  in
                                               (uu____6779,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6772
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6821 =
                                               let uu____6828 =
                                                 let uu____6829 =
                                                   let uu____6840 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6840)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6829
                                                  in
                                               (uu____6828,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6821
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
                                           ((let uu____6865 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6865);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____6880 =
                       let uu____6887 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6887,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6880  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6899 =
                       let uu____6906 =
                         let uu____6907 =
                           let uu____6918 =
                             let uu____6919 =
                               let uu____6924 =
                                 let uu____6925 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6925
                                  in
                               (f_has_t, uu____6924)  in
                             FStar_SMTEncoding_Util.mkImp uu____6919  in
                           ([[f_has_t]], [fsym], uu____6918)  in
                         mkForall_fuel uu____6907  in
                       (uu____6906, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6899  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6952 ->
           let uu____6959 =
             let uu____6964 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6964 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6971;
                 FStar_Syntax_Syntax.vars = uu____6972;_} ->
                 let uu____6979 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6979 with
                  | (b,f1) ->
                      let uu____7004 =
                        let uu____7005 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____7005  in
                      (uu____7004, f1))
             | uu____7014 -> failwith "impossible"  in
           (match uu____6959 with
            | (x,f) ->
                let uu____7025 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____7025 with
                 | (base_t,decls) ->
                     let uu____7036 = gen_term_var env x  in
                     (match uu____7036 with
                      | (x1,xtm,env') ->
                          let uu____7050 = encode_formula f env'  in
                          (match uu____7050 with
                           | (refinement,decls') ->
                               let uu____7061 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____7061 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____7077 =
                                        let uu____7080 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____7087 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____7080
                                          uu____7087
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____7077
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____7120  ->
                                              match uu____7120 with
                                              | (y,uu____7126) ->
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
                                    let uu____7159 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____7159 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____7167 =
                                           let uu____7168 =
                                             let uu____7175 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____7175)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7168
                                            in
                                         (uu____7167,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____7196 =
                                             let uu____7197 =
                                               let uu____7198 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____7198
                                                in
                                             Prims.strcat module_name
                                               uu____7197
                                              in
                                           varops.mk_unique uu____7196  in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____7212 =
                                             let uu____7219 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____7219)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____7212
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1
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
                                           let uu____7234 =
                                             let uu____7241 =
                                               let uu____7242 =
                                                 let uu____7253 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____7253)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7242
                                                in
                                             (uu____7241,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7234
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
                                           let uu____7279 =
                                             let uu____7286 =
                                               let uu____7287 =
                                                 let uu____7298 =
                                                   let uu____7299 =
                                                     let uu____7304 =
                                                       let uu____7305 =
                                                         let uu____7316 =
                                                           FStar_SMTEncoding_Util.mkAnd
                                                             (x_has_base_t,
                                                               refinement)
                                                            in
                                                         ([], [xx],
                                                           uu____7316)
                                                          in
                                                       FStar_SMTEncoding_Util.mkExists
                                                         uu____7305
                                                        in
                                                     (uu____7304, valid_t)
                                                      in
                                                   FStar_SMTEncoding_Util.mkIff
                                                     uu____7299
                                                    in
                                                 ([[valid_t]], cvars1,
                                                   uu____7298)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7287
                                                in
                                             (uu____7286,
                                               (FStar_Pervasives_Native.Some
                                                  "validity axiom for refinement"),
                                               (Prims.strcat "ref_valid_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7279
                                            in
                                         let t_kinding =
                                           let uu____7354 =
                                             let uu____7361 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____7361,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7354
                                            in
                                         let t_interp =
                                           let uu____7379 =
                                             let uu____7386 =
                                               let uu____7387 =
                                                 let uu____7398 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7398)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7387
                                                in
                                             let uu____7421 =
                                               let uu____7424 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7424
                                                in
                                             (uu____7386, uu____7421,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7379
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
                                         ((let uu____7431 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7431);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7461 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7461  in
           let uu____7462 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____7462 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7474 =
                    let uu____7481 =
                      let uu____7482 =
                        let uu____7483 =
                          let uu____7484 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7484
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7483  in
                      varops.mk_unique uu____7482  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7481)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7474  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7489 ->
           let uu____7504 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7504 with
            | (head1,args_e) ->
                let uu____7545 =
                  let uu____7558 =
                    let uu____7559 = FStar_Syntax_Subst.compress head1  in
                    uu____7559.FStar_Syntax_Syntax.n  in
                  (uu____7558, args_e)  in
                (match uu____7545 with
                 | uu____7574 when head_redex env head1 ->
                     let uu____7587 = whnf env t  in
                     encode_term uu____7587 env
                 | uu____7588 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7607 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7621;
                       FStar_Syntax_Syntax.vars = uu____7622;_},uu____7623),uu____7624::
                    (v1,uu____7626)::(v2,uu____7628)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7679 = encode_term v1 env  in
                     (match uu____7679 with
                      | (v11,decls1) ->
                          let uu____7690 = encode_term v2 env  in
                          (match uu____7690 with
                           | (v21,decls2) ->
                               let uu____7701 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7701,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7705::(v1,uu____7707)::(v2,uu____7709)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7756 = encode_term v1 env  in
                     (match uu____7756 with
                      | (v11,decls1) ->
                          let uu____7767 = encode_term v2 env  in
                          (match uu____7767 with
                           | (v21,decls2) ->
                               let uu____7778 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7778,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7781) ->
                     let e0 =
                       let uu____7799 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7799
                        in
                     ((let uu____7807 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7807
                       then
                         let uu____7808 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7808
                       else ());
                      (let e =
                         let uu____7813 =
                           let uu____7814 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7815 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7814
                             uu____7815
                            in
                         uu____7813 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7824),(arg,uu____7826)::[]) -> encode_term arg env
                 | uu____7851 ->
                     let uu____7864 = encode_args args_e env  in
                     (match uu____7864 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7919 = encode_term head1 env  in
                            match uu____7919 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7983 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7983 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____8061  ->
                                                 fun uu____8062  ->
                                                   match (uu____8061,
                                                           uu____8062)
                                                   with
                                                   | ((bv,uu____8084),
                                                      (a,uu____8086)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____8104 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____8104
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____8109 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____8109 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____8124 =
                                                   let uu____8131 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____8140 =
                                                     let uu____8141 =
                                                       let uu____8142 =
                                                         let uu____8143 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____8143
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____8142
                                                        in
                                                     varops.mk_unique
                                                       uu____8141
                                                      in
                                                   (uu____8131,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____8140)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____8124
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____8160 = lookup_free_var_sym env fv  in
                            match uu____8160 with
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
                                   FStar_Syntax_Syntax.pos = uu____8191;
                                   FStar_Syntax_Syntax.vars = uu____8192;_},uu____8193)
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
                                   FStar_Syntax_Syntax.pos = uu____8204;
                                   FStar_Syntax_Syntax.vars = uu____8205;_},uu____8206)
                                ->
                                let uu____8211 =
                                  let uu____8212 =
                                    let uu____8217 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8217
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8212
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8211
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____8247 =
                                  let uu____8248 =
                                    let uu____8253 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____8253
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____8248
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____8247
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8282,(FStar_Util.Inl t1,uu____8284),uu____8285)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8334,(FStar_Util.Inr c,uu____8336),uu____8337)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8386 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8413 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8413
                                  in
                               let uu____8414 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8414 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8430;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8431;_},uu____8432)
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
                                     | uu____8446 ->
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
           let uu____8495 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8495 with
            | (bs1,body1,opening) ->
                let fallback uu____8518 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8525 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8525, [decl])  in
                let is_impure rc =
                  let uu____8532 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8532 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8542 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____8542
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8562 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8562
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8566 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8566)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8573 =
                         let uu____8574 =
                           FStar_Syntax_Print.term_to_string t0  in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____8574
                          in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____8573);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8576 =
                       (is_impure rc) &&
                         (let uu____8578 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8578)
                        in
                     if uu____8576
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8585 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8585 with
                        | (vars,guards,envbody,decls,uu____8610) ->
                            let body2 =
                              let uu____8624 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8624
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8626 = encode_term body2 envbody  in
                            (match uu____8626 with
                             | (body3,decls') ->
                                 let uu____8637 =
                                   let uu____8646 = codomain_eff rc  in
                                   match uu____8646 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8665 = encode_term tfun env
                                          in
                                       (match uu____8665 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8637 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8697 =
                                          let uu____8708 =
                                            let uu____8709 =
                                              let uu____8714 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8714, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8709
                                             in
                                          ([], vars, uu____8708)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8697
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8726 =
                                              let uu____8729 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8729
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8726
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8748 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8748 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8756 =
                                             let uu____8757 =
                                               let uu____8764 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8764)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8757
                                              in
                                           (uu____8756,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8775 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8775 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8786 =
                                                    let uu____8787 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8787 = cache_size
                                                     in
                                                  if uu____8786
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____8803 =
                                                      let uu____8804 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8804
                                                       in
                                                    varops.mk_unique
                                                      uu____8803
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____8811 =
                                                    let uu____8818 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8818)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8811
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____8836 =
                                                        let uu____8837 =
                                                          let uu____8844 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8844,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8837
                                                         in
                                                      [uu____8836]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8857 =
                                                    let uu____8864 =
                                                      let uu____8865 =
                                                        let uu____8876 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8876)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8865
                                                       in
                                                    (uu____8864,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8857
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
                                                ((let uu____8893 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8893);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8896,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8897;
                          FStar_Syntax_Syntax.lbunivs = uu____8898;
                          FStar_Syntax_Syntax.lbtyp = uu____8899;
                          FStar_Syntax_Syntax.lbeff = uu____8900;
                          FStar_Syntax_Syntax.lbdef = uu____8901;_}::uu____8902),uu____8903)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8929;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8931;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8952 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec"  in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None)
                in
             let uu____8972 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort)
                in
             (uu____8972, [decl_e])))
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
              let uu____9027 = encode_term e1 env  in
              match uu____9027 with
              | (ee1,decls1) ->
                  let uu____9038 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____9038 with
                   | (xs,e21) ->
                       let uu____9063 = FStar_List.hd xs  in
                       (match uu____9063 with
                        | (x1,uu____9077) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____9079 = encode_body e21 env'  in
                            (match uu____9079 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and encode_match :
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
            let uu____9111 =
              let uu____9118 =
                let uu____9119 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____9119  in
              gen_term_var env uu____9118  in
            match uu____9111 with
            | (scrsym,scr',env1) ->
                let uu____9127 = encode_term e env1  in
                (match uu____9127 with
                 | (scr,decls) ->
                     let uu____9138 =
                       let encode_branch b uu____9163 =
                         match uu____9163 with
                         | (else_case,decls1) ->
                             let uu____9182 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____9182 with
                              | (p,w,br) ->
                                  let uu____9208 = encode_pat env1 p  in
                                  (match uu____9208 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____9245  ->
                                                   match uu____9245 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____9252 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____9274 =
                                               encode_term w1 env2  in
                                             (match uu____9274 with
                                              | (w2,decls2) ->
                                                  let uu____9287 =
                                                    let uu____9288 =
                                                      let uu____9293 =
                                                        let uu____9294 =
                                                          let uu____9299 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9299)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9294
                                                         in
                                                      (guard, uu____9293)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____9288
                                                     in
                                                  (uu____9287, decls2))
                                          in
                                       (match uu____9252 with
                                        | (guard1,decls2) ->
                                            let uu____9312 =
                                              encode_br br env2  in
                                            (match uu____9312 with
                                             | (br1,decls3) ->
                                                 let uu____9325 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9325,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____9138 with
                      | (match_tm,decls1) ->
                          let uu____9344 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9344, decls1)))

and encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9384 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9384
       then
         let uu____9385 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9385
       else ());
      (let uu____9387 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9387 with
       | (vars,pat_term) ->
           let uu____9404 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9457  ->
                     fun v1  ->
                       match uu____9457 with
                       | (env1,vars1) ->
                           let uu____9509 = gen_term_var env1 v1  in
                           (match uu____9509 with
                            | (xx,uu____9531,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9404 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9610 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9611 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9612 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9620 =
                        let uu____9625 = encode_const c  in
                        (scrutinee, uu____9625)  in
                      FStar_SMTEncoding_Util.mkEq uu____9620
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9646 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9646 with
                        | (uu____9653,uu____9654::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9657 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9690  ->
                                  match uu____9690 with
                                  | (arg,uu____9698) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9704 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9704))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9731) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9762 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9785 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9829  ->
                                  match uu____9829 with
                                  | (arg,uu____9843) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9849 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9849))
                         in
                      FStar_All.pipe_right uu____9785 FStar_List.flatten
                   in
                let pat_term1 uu____9877 = encode_term pat_term env1  in
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
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____9887 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9925  ->
                fun uu____9926  ->
                  match (uu____9925, uu____9926) with
                  | ((tms,decls),(t,uu____9962)) ->
                      let uu____9983 = encode_term t env  in
                      (match uu____9983 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9887 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____10040 = FStar_Syntax_Util.list_elements e  in
        match uu____10040 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             [])
         in
      let one_pat p =
        let uu____10061 =
          let uu____10076 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____10076 FStar_Syntax_Util.head_and_args
           in
        match uu____10061 with
        | (head1,args) ->
            let uu____10115 =
              let uu____10128 =
                let uu____10129 = FStar_Syntax_Util.un_uinst head1  in
                uu____10129.FStar_Syntax_Syntax.n  in
              (uu____10128, args)  in
            (match uu____10115 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____10143,uu____10144)::(e,uu____10146)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____10181 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____10217 =
            let uu____10232 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____10232 FStar_Syntax_Util.head_and_args
             in
          match uu____10217 with
          | (head1,args) ->
              let uu____10273 =
                let uu____10286 =
                  let uu____10287 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10287.FStar_Syntax_Syntax.n  in
                (uu____10286, args)  in
              (match uu____10273 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10304)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10331 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10353 = smt_pat_or1 t1  in
            (match uu____10353 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10369 = list_elements1 e  in
                 FStar_All.pipe_right uu____10369
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10387 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10387
                           (FStar_List.map one_pat)))
             | uu____10398 ->
                 let uu____10403 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10403])
        | uu____10424 ->
            let uu____10427 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10427]
         in
      let uu____10448 =
        let uu____10467 =
          let uu____10468 = FStar_Syntax_Subst.compress t  in
          uu____10468.FStar_Syntax_Syntax.n  in
        match uu____10467 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10507 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10507 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10550;
                        FStar_Syntax_Syntax.effect_name = uu____10551;
                        FStar_Syntax_Syntax.result_typ = uu____10552;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10554)::(post,uu____10556)::(pats,uu____10558)::[];
                        FStar_Syntax_Syntax.flags = uu____10559;_}
                      ->
                      let uu____10600 = lemma_pats pats  in
                      (binders1, pre, post, uu____10600)
                  | uu____10617 -> failwith "impos"))
        | uu____10636 -> failwith "Impos"  in
      match uu____10448 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___140_10684 = env  in
            {
              bindings = (uu___140_10684.bindings);
              depth = (uu___140_10684.depth);
              tcenv = (uu___140_10684.tcenv);
              warn = (uu___140_10684.warn);
              cache = (uu___140_10684.cache);
              nolabels = (uu___140_10684.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___140_10684.encode_non_total_function_typ);
              current_module_name = (uu___140_10684.current_module_name)
            }  in
          let uu____10685 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10685 with
           | (vars,guards,env2,decls,uu____10710) ->
               let uu____10723 =
                 let uu____10736 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10780 =
                             let uu____10789 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2))
                                in
                             FStar_All.pipe_right uu____10789
                               FStar_List.unzip
                              in
                           match uu____10780 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10736 FStar_List.unzip  in
               (match uu____10723 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let env3 =
                      let uu___141_10898 = env2  in
                      {
                        bindings = (uu___141_10898.bindings);
                        depth = (uu___141_10898.depth);
                        tcenv = (uu___141_10898.tcenv);
                        warn = (uu___141_10898.warn);
                        cache = (uu___141_10898.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___141_10898.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___141_10898.encode_non_total_function_typ);
                        current_module_name =
                          (uu___141_10898.current_module_name)
                      }  in
                    let uu____10899 =
                      let uu____10904 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10904 env3  in
                    (match uu____10899 with
                     | (pre1,decls'') ->
                         let uu____10911 =
                           let uu____10916 = FStar_Syntax_Util.unmeta post
                              in
                           encode_formula uu____10916 env3  in
                         (match uu____10911 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10926 =
                                let uu____10927 =
                                  let uu____10938 =
                                    let uu____10939 =
                                      let uu____10944 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10944, post1)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10939
                                     in
                                  (pats, vars, uu____10938)  in
                                FStar_SMTEncoding_Util.mkForall uu____10927
                                 in
                              (uu____10926, decls1)))))

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10963 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10963
        then
          let uu____10964 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10965 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10964 uu____10965
        else ()  in
      let enc f r l =
        let uu____10998 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____11026 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____11026 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10998 with
        | (decls,args) ->
            let uu____11055 =
              let uu___142_11056 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___142_11056.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___142_11056.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11055, decls)
         in
      let const_op f r uu____11087 =
        let uu____11100 = f r  in (uu____11100, [])  in
      let un_op f l =
        let uu____11119 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11119  in
      let bin_op f uu___116_11135 =
        match uu___116_11135 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11146 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11180 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11203  ->
                 match uu____11203 with
                 | (t,uu____11217) ->
                     let uu____11218 = encode_formula t env  in
                     (match uu____11218 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11180 with
        | (decls,phis) ->
            let uu____11247 =
              let uu___143_11248 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___143_11248.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___143_11248.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11247, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11309  ->
               match uu____11309 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11328) -> false
                    | uu____11329 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11344 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11344
        else
          (let uu____11358 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11358 r rf)
         in
      let mk_imp1 r uu___117_11383 =
        match uu___117_11383 with
        | (lhs,uu____11389)::(rhs,uu____11391)::[] ->
            let uu____11418 = encode_formula rhs env  in
            (match uu____11418 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11433) ->
                      (l1, decls1)
                  | uu____11438 ->
                      let uu____11439 = encode_formula lhs env  in
                      (match uu____11439 with
                       | (l2,decls2) ->
                           let uu____11450 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11450, (FStar_List.append decls1 decls2)))))
        | uu____11453 -> failwith "impossible"  in
      let mk_ite r uu___118_11474 =
        match uu___118_11474 with
        | (guard,uu____11480)::(_then,uu____11482)::(_else,uu____11484)::[]
            ->
            let uu____11521 = encode_formula guard env  in
            (match uu____11521 with
             | (g,decls1) ->
                 let uu____11532 = encode_formula _then env  in
                 (match uu____11532 with
                  | (t,decls2) ->
                      let uu____11543 = encode_formula _else env  in
                      (match uu____11543 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11557 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11582 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11582  in
      let connectives =
        let uu____11600 =
          let uu____11613 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11613)  in
        let uu____11630 =
          let uu____11645 =
            let uu____11658 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11658)  in
          let uu____11675 =
            let uu____11690 =
              let uu____11705 =
                let uu____11718 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11718)  in
              let uu____11735 =
                let uu____11750 =
                  let uu____11765 =
                    let uu____11778 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11778)  in
                  [uu____11765;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11750  in
              uu____11705 :: uu____11735  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11690  in
          uu____11645 :: uu____11675  in
        uu____11600 :: uu____11630  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12099 = encode_formula phi' env  in
            (match uu____12099 with
             | (phi2,decls) ->
                 let uu____12110 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12110, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12111 ->
            let uu____12118 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12118 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12157 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12157 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12169;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12171;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12192 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12192 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12239::(x,uu____12241)::(t,uu____12243)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12290 = encode_term x env  in
                 (match uu____12290 with
                  | (x1,decls) ->
                      let uu____12301 = encode_term t env  in
                      (match uu____12301 with
                       | (t1,decls') ->
                           let uu____12312 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12312, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12317)::(msg,uu____12319)::(phi2,uu____12321)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12366 =
                   let uu____12371 =
                     let uu____12372 = FStar_Syntax_Subst.compress r  in
                     uu____12372.FStar_Syntax_Syntax.n  in
                   let uu____12375 =
                     let uu____12376 = FStar_Syntax_Subst.compress msg  in
                     uu____12376.FStar_Syntax_Syntax.n  in
                   (uu____12371, uu____12375)  in
                 (match uu____12366 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12385))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  ((FStar_Util.string_of_unicode s), r1,
                                    false)))) FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12395 -> fallback phi2)
             | uu____12400 when head_redex env head2 ->
                 let uu____12413 = whnf env phi1  in
                 encode_formula uu____12413 env
             | uu____12414 ->
                 let uu____12427 = encode_term phi1 env  in
                 (match uu____12427 with
                  | (tt,decls) ->
                      let uu____12438 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___144_12441 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___144_12441.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___144_12441.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12438, decls)))
        | uu____12442 ->
            let uu____12443 = encode_term phi1 env  in
            (match uu____12443 with
             | (tt,decls) ->
                 let uu____12454 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___145_12457 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___145_12457.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___145_12457.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12454, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12493 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12493 with
        | (vars,guards,env2,decls,uu____12532) ->
            let uu____12545 =
              let uu____12558 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12606 =
                          let uu____12615 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12645  ->
                                    match uu____12645 with
                                    | (t,uu____12655) ->
                                        encode_term t
                                          (let uu___146_12657 = env2  in
                                           {
                                             bindings =
                                               (uu___146_12657.bindings);
                                             depth = (uu___146_12657.depth);
                                             tcenv = (uu___146_12657.tcenv);
                                             warn = (uu___146_12657.warn);
                                             cache = (uu___146_12657.cache);
                                             nolabels =
                                               (uu___146_12657.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___146_12657.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___146_12657.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12615 FStar_List.unzip
                           in
                        match uu____12606 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12558 FStar_List.unzip  in
            (match uu____12545 with
             | (pats,decls') ->
                 let uu____12756 = encode_formula body env2  in
                 (match uu____12756 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12788;
                             FStar_SMTEncoding_Term.rng = uu____12789;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12804 -> guards  in
                      let uu____12809 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12809, body1,
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
                (fun uu____12869  ->
                   match uu____12869 with
                   | (x,uu____12875) ->
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
               let uu____12883 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12895 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12895) uu____12883 tl1
                in
             let uu____12898 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12925  ->
                       match uu____12925 with
                       | (b,uu____12931) ->
                           let uu____12932 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12932))
                in
             (match uu____12898 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12938) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12952 =
                    let uu____12953 = FStar_Syntax_Print.bv_to_string x  in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____12953
                     in
                  FStar_Errors.warn pos uu____12952)
          in
       let uu____12954 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12954 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12963 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13021  ->
                     match uu____13021 with
                     | (l,uu____13035) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12963 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13068,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13108 = encode_q_body env vars pats body  in
             match uu____13108 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13153 =
                     let uu____13164 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13164)  in
                   FStar_SMTEncoding_Term.mkForall uu____13153
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13183 = encode_q_body env vars pats body  in
             match uu____13183 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13227 =
                   let uu____13228 =
                     let uu____13239 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13239)  in
                   FStar_SMTEncoding_Term.mkExists uu____13228
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13227, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
    ;
  is: FStar_Ident.lident -> Prims.bool }
let __proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
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
  let uu____13337 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13337 with
  | (asym,a) ->
      let uu____13344 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13344 with
       | (xsym,x) ->
           let uu____13351 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13351 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13395 =
                      let uu____13406 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13406, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13395  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13432 =
                      let uu____13439 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13439)  in
                    FStar_SMTEncoding_Util.mkApp uu____13432  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13452 =
                    let uu____13455 =
                      let uu____13458 =
                        let uu____13461 =
                          let uu____13462 =
                            let uu____13469 =
                              let uu____13470 =
                                let uu____13481 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13481)  in
                              FStar_SMTEncoding_Util.mkForall uu____13470  in
                            (uu____13469, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13462  in
                        let uu____13498 =
                          let uu____13501 =
                            let uu____13502 =
                              let uu____13509 =
                                let uu____13510 =
                                  let uu____13521 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13521)  in
                                FStar_SMTEncoding_Util.mkForall uu____13510
                                 in
                              (uu____13509,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13502  in
                          [uu____13501]  in
                        uu____13461 :: uu____13498  in
                      xtok_decl :: uu____13458  in
                    xname_decl :: uu____13455  in
                  (xtok1, uu____13452)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13612 =
                    let uu____13625 =
                      let uu____13634 =
                        let uu____13635 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13635
                         in
                      quant axy uu____13634  in
                    (FStar_Parser_Const.op_Eq, uu____13625)  in
                  let uu____13644 =
                    let uu____13659 =
                      let uu____13672 =
                        let uu____13681 =
                          let uu____13682 =
                            let uu____13683 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13683  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13682
                           in
                        quant axy uu____13681  in
                      (FStar_Parser_Const.op_notEq, uu____13672)  in
                    let uu____13692 =
                      let uu____13707 =
                        let uu____13720 =
                          let uu____13729 =
                            let uu____13730 =
                              let uu____13731 =
                                let uu____13736 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13737 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13736, uu____13737)  in
                              FStar_SMTEncoding_Util.mkLT uu____13731  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13730
                             in
                          quant xy uu____13729  in
                        (FStar_Parser_Const.op_LT, uu____13720)  in
                      let uu____13746 =
                        let uu____13761 =
                          let uu____13774 =
                            let uu____13783 =
                              let uu____13784 =
                                let uu____13785 =
                                  let uu____13790 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13791 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13790, uu____13791)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13785  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13784
                               in
                            quant xy uu____13783  in
                          (FStar_Parser_Const.op_LTE, uu____13774)  in
                        let uu____13800 =
                          let uu____13815 =
                            let uu____13828 =
                              let uu____13837 =
                                let uu____13838 =
                                  let uu____13839 =
                                    let uu____13844 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13845 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13844, uu____13845)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13839  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13838
                                 in
                              quant xy uu____13837  in
                            (FStar_Parser_Const.op_GT, uu____13828)  in
                          let uu____13854 =
                            let uu____13869 =
                              let uu____13882 =
                                let uu____13891 =
                                  let uu____13892 =
                                    let uu____13893 =
                                      let uu____13898 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13899 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13898, uu____13899)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13893
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13892
                                   in
                                quant xy uu____13891  in
                              (FStar_Parser_Const.op_GTE, uu____13882)  in
                            let uu____13908 =
                              let uu____13923 =
                                let uu____13936 =
                                  let uu____13945 =
                                    let uu____13946 =
                                      let uu____13947 =
                                        let uu____13952 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13953 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13952, uu____13953)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13947
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13946
                                     in
                                  quant xy uu____13945  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13936)
                                 in
                              let uu____13962 =
                                let uu____13977 =
                                  let uu____13990 =
                                    let uu____13999 =
                                      let uu____14000 =
                                        let uu____14001 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____14001
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____14000
                                       in
                                    quant qx uu____13999  in
                                  (FStar_Parser_Const.op_Minus, uu____13990)
                                   in
                                let uu____14010 =
                                  let uu____14025 =
                                    let uu____14038 =
                                      let uu____14047 =
                                        let uu____14048 =
                                          let uu____14049 =
                                            let uu____14054 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14055 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14054, uu____14055)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14049
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14048
                                         in
                                      quant xy uu____14047  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14038)
                                     in
                                  let uu____14064 =
                                    let uu____14079 =
                                      let uu____14092 =
                                        let uu____14101 =
                                          let uu____14102 =
                                            let uu____14103 =
                                              let uu____14108 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14109 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14108, uu____14109)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14103
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14102
                                           in
                                        quant xy uu____14101  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14092)
                                       in
                                    let uu____14118 =
                                      let uu____14133 =
                                        let uu____14146 =
                                          let uu____14155 =
                                            let uu____14156 =
                                              let uu____14157 =
                                                let uu____14162 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14163 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14162, uu____14163)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14157
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14156
                                             in
                                          quant xy uu____14155  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14146)
                                         in
                                      let uu____14172 =
                                        let uu____14187 =
                                          let uu____14200 =
                                            let uu____14209 =
                                              let uu____14210 =
                                                let uu____14211 =
                                                  let uu____14216 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14217 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14216, uu____14217)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14211
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14210
                                               in
                                            quant xy uu____14209  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14200)
                                           in
                                        let uu____14226 =
                                          let uu____14241 =
                                            let uu____14254 =
                                              let uu____14263 =
                                                let uu____14264 =
                                                  let uu____14265 =
                                                    let uu____14270 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____14271 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____14270,
                                                      uu____14271)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14265
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14264
                                                 in
                                              quant xy uu____14263  in
                                            (FStar_Parser_Const.op_And,
                                              uu____14254)
                                             in
                                          let uu____14280 =
                                            let uu____14295 =
                                              let uu____14308 =
                                                let uu____14317 =
                                                  let uu____14318 =
                                                    let uu____14319 =
                                                      let uu____14324 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14325 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14324,
                                                        uu____14325)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14319
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14318
                                                   in
                                                quant xy uu____14317  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14308)
                                               in
                                            let uu____14334 =
                                              let uu____14349 =
                                                let uu____14362 =
                                                  let uu____14371 =
                                                    let uu____14372 =
                                                      let uu____14373 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14373
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14372
                                                     in
                                                  quant qx uu____14371  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14362)
                                                 in
                                              [uu____14349]  in
                                            uu____14295 :: uu____14334  in
                                          uu____14241 :: uu____14280  in
                                        uu____14187 :: uu____14226  in
                                      uu____14133 :: uu____14172  in
                                    uu____14079 :: uu____14118  in
                                  uu____14025 :: uu____14064  in
                                uu____13977 :: uu____14010  in
                              uu____13923 :: uu____13962  in
                            uu____13869 :: uu____13908  in
                          uu____13815 :: uu____13854  in
                        uu____13761 :: uu____13800  in
                      uu____13707 :: uu____13746  in
                    uu____13659 :: uu____13692  in
                  uu____13612 :: uu____13644  in
                let mk1 l v1 =
                  let uu____14587 =
                    let uu____14596 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14654  ->
                              match uu____14654 with
                              | (l',uu____14668) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14596
                      (FStar_Option.map
                         (fun uu____14728  ->
                            match uu____14728 with | (uu____14747,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14587 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14818  ->
                          match uu____14818 with
                          | (l',uu____14832) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____14873 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14873 with
        | (xxsym,xx) ->
            let uu____14880 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14880 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14890 =
                   let uu____14897 =
                     let uu____14898 =
                       let uu____14909 =
                         let uu____14910 =
                           let uu____14915 =
                             let uu____14916 =
                               let uu____14921 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14921)  in
                             FStar_SMTEncoding_Util.mkEq uu____14916  in
                           (xx_has_type, uu____14915)  in
                         FStar_SMTEncoding_Util.mkImp uu____14910  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14909)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14898  in
                   let uu____14946 =
                     let uu____14947 =
                       let uu____14948 =
                         let uu____14949 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14949  in
                       Prims.strcat module_name uu____14948  in
                     varops.mk_unique uu____14947  in
                   (uu____14897, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14946)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14890)
  
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
    let uu____14989 =
      let uu____14990 =
        let uu____14997 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14997, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14990  in
    let uu____15000 =
      let uu____15003 =
        let uu____15004 =
          let uu____15011 =
            let uu____15012 =
              let uu____15023 =
                let uu____15024 =
                  let uu____15029 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15029)  in
                FStar_SMTEncoding_Util.mkImp uu____15024  in
              ([[typing_pred]], [xx], uu____15023)  in
            mkForall_fuel uu____15012  in
          (uu____15011, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15004  in
      [uu____15003]  in
    uu____14989 :: uu____15000  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15071 =
      let uu____15072 =
        let uu____15079 =
          let uu____15080 =
            let uu____15091 =
              let uu____15096 =
                let uu____15099 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____15099]  in
              [uu____15096]  in
            let uu____15104 =
              let uu____15105 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15105 tt  in
            (uu____15091, [bb], uu____15104)  in
          FStar_SMTEncoding_Util.mkForall uu____15080  in
        (uu____15079, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15072  in
    let uu____15126 =
      let uu____15129 =
        let uu____15130 =
          let uu____15137 =
            let uu____15138 =
              let uu____15149 =
                let uu____15150 =
                  let uu____15155 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____15155)  in
                FStar_SMTEncoding_Util.mkImp uu____15150  in
              ([[typing_pred]], [xx], uu____15149)  in
            mkForall_fuel uu____15138  in
          (uu____15137, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15130  in
      [uu____15129]  in
    uu____15071 :: uu____15126  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____15205 =
        let uu____15206 =
          let uu____15213 =
            let uu____15216 =
              let uu____15219 =
                let uu____15222 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15223 =
                  let uu____15226 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15226]  in
                uu____15222 :: uu____15223  in
              tt :: uu____15219  in
            tt :: uu____15216  in
          ("Prims.Precedes", uu____15213)  in
        FStar_SMTEncoding_Util.mkApp uu____15206  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15205  in
    let precedes_y_x =
      let uu____15230 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15230  in
    let uu____15233 =
      let uu____15234 =
        let uu____15241 =
          let uu____15242 =
            let uu____15253 =
              let uu____15258 =
                let uu____15261 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15261]  in
              [uu____15258]  in
            let uu____15266 =
              let uu____15267 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15267 tt  in
            (uu____15253, [bb], uu____15266)  in
          FStar_SMTEncoding_Util.mkForall uu____15242  in
        (uu____15241, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15234  in
    let uu____15288 =
      let uu____15291 =
        let uu____15292 =
          let uu____15299 =
            let uu____15300 =
              let uu____15311 =
                let uu____15312 =
                  let uu____15317 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15317)  in
                FStar_SMTEncoding_Util.mkImp uu____15312  in
              ([[typing_pred]], [xx], uu____15311)  in
            mkForall_fuel uu____15300  in
          (uu____15299, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15292  in
      let uu____15342 =
        let uu____15345 =
          let uu____15346 =
            let uu____15353 =
              let uu____15354 =
                let uu____15365 =
                  let uu____15366 =
                    let uu____15371 =
                      let uu____15372 =
                        let uu____15375 =
                          let uu____15378 =
                            let uu____15381 =
                              let uu____15382 =
                                let uu____15387 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15388 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15387, uu____15388)  in
                              FStar_SMTEncoding_Util.mkGT uu____15382  in
                            let uu____15389 =
                              let uu____15392 =
                                let uu____15393 =
                                  let uu____15398 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15399 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15398, uu____15399)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15393  in
                              let uu____15400 =
                                let uu____15403 =
                                  let uu____15404 =
                                    let uu____15409 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15410 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15409, uu____15410)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15404  in
                                [uu____15403]  in
                              uu____15392 :: uu____15400  in
                            uu____15381 :: uu____15389  in
                          typing_pred_y :: uu____15378  in
                        typing_pred :: uu____15375  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15372  in
                    (uu____15371, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15366  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15365)
                 in
              mkForall_fuel uu____15354  in
            (uu____15353,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15346  in
        [uu____15345]  in
      uu____15291 :: uu____15342  in
    uu____15233 :: uu____15288  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15456 =
      let uu____15457 =
        let uu____15464 =
          let uu____15465 =
            let uu____15476 =
              let uu____15481 =
                let uu____15484 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15484]  in
              [uu____15481]  in
            let uu____15489 =
              let uu____15490 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15490 tt  in
            (uu____15476, [bb], uu____15489)  in
          FStar_SMTEncoding_Util.mkForall uu____15465  in
        (uu____15464, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15457  in
    let uu____15511 =
      let uu____15514 =
        let uu____15515 =
          let uu____15522 =
            let uu____15523 =
              let uu____15534 =
                let uu____15535 =
                  let uu____15540 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15540)  in
                FStar_SMTEncoding_Util.mkImp uu____15535  in
              ([[typing_pred]], [xx], uu____15534)  in
            mkForall_fuel uu____15523  in
          (uu____15522, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15515  in
      [uu____15514]  in
    uu____15456 :: uu____15511  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15593 =
      let uu____15594 =
        let uu____15601 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15601, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15594  in
    [uu____15593]  in
  let mk_and_interp env conj uu____15613 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15638 =
      let uu____15639 =
        let uu____15646 =
          let uu____15647 =
            let uu____15658 =
              let uu____15659 =
                let uu____15664 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15664, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15659  in
            ([[l_and_a_b]], [aa; bb], uu____15658)  in
          FStar_SMTEncoding_Util.mkForall uu____15647  in
        (uu____15646, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15639  in
    [uu____15638]  in
  let mk_or_interp env disj uu____15702 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15727 =
      let uu____15728 =
        let uu____15735 =
          let uu____15736 =
            let uu____15747 =
              let uu____15748 =
                let uu____15753 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15753, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15748  in
            ([[l_or_a_b]], [aa; bb], uu____15747)  in
          FStar_SMTEncoding_Util.mkForall uu____15736  in
        (uu____15735, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15728  in
    [uu____15727]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15816 =
      let uu____15817 =
        let uu____15824 =
          let uu____15825 =
            let uu____15836 =
              let uu____15837 =
                let uu____15842 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15842, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15837  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15836)  in
          FStar_SMTEncoding_Util.mkForall uu____15825  in
        (uu____15824, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15817  in
    [uu____15816]  in
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
    let uu____15915 =
      let uu____15916 =
        let uu____15923 =
          let uu____15924 =
            let uu____15935 =
              let uu____15936 =
                let uu____15941 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15941, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15936  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15935)  in
          FStar_SMTEncoding_Util.mkForall uu____15924  in
        (uu____15923, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15916  in
    [uu____15915]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16012 =
      let uu____16013 =
        let uu____16020 =
          let uu____16021 =
            let uu____16032 =
              let uu____16033 =
                let uu____16038 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____16038, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16033  in
            ([[l_imp_a_b]], [aa; bb], uu____16032)  in
          FStar_SMTEncoding_Util.mkForall uu____16021  in
        (uu____16020, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16013  in
    [uu____16012]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16101 =
      let uu____16102 =
        let uu____16109 =
          let uu____16110 =
            let uu____16121 =
              let uu____16122 =
                let uu____16127 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____16127, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16122  in
            ([[l_iff_a_b]], [aa; bb], uu____16121)  in
          FStar_SMTEncoding_Util.mkForall uu____16110  in
        (uu____16109, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16102  in
    [uu____16101]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____16179 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16179  in
    let uu____16182 =
      let uu____16183 =
        let uu____16190 =
          let uu____16191 =
            let uu____16202 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____16202)  in
          FStar_SMTEncoding_Util.mkForall uu____16191  in
        (uu____16190, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16183  in
    [uu____16182]  in
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
      let uu____16262 =
        let uu____16269 =
          let uu____16272 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16272]  in
        ("Valid", uu____16269)  in
      FStar_SMTEncoding_Util.mkApp uu____16262  in
    let uu____16275 =
      let uu____16276 =
        let uu____16283 =
          let uu____16284 =
            let uu____16295 =
              let uu____16296 =
                let uu____16301 =
                  let uu____16302 =
                    let uu____16313 =
                      let uu____16318 =
                        let uu____16321 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16321]  in
                      [uu____16318]  in
                    let uu____16326 =
                      let uu____16327 =
                        let uu____16332 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16332, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16327  in
                    (uu____16313, [xx1], uu____16326)  in
                  FStar_SMTEncoding_Util.mkForall uu____16302  in
                (uu____16301, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16296  in
            ([[l_forall_a_b]], [aa; bb], uu____16295)  in
          FStar_SMTEncoding_Util.mkForall uu____16284  in
        (uu____16283, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16276  in
    [uu____16275]  in
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
      let uu____16414 =
        let uu____16421 =
          let uu____16424 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16424]  in
        ("Valid", uu____16421)  in
      FStar_SMTEncoding_Util.mkApp uu____16414  in
    let uu____16427 =
      let uu____16428 =
        let uu____16435 =
          let uu____16436 =
            let uu____16447 =
              let uu____16448 =
                let uu____16453 =
                  let uu____16454 =
                    let uu____16465 =
                      let uu____16470 =
                        let uu____16473 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16473]  in
                      [uu____16470]  in
                    let uu____16478 =
                      let uu____16479 =
                        let uu____16484 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16484, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16479  in
                    (uu____16465, [xx1], uu____16478)  in
                  FStar_SMTEncoding_Util.mkExists uu____16454  in
                (uu____16453, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16448  in
            ([[l_exists_a_b]], [aa; bb], uu____16447)  in
          FStar_SMTEncoding_Util.mkForall uu____16436  in
        (uu____16435, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16428  in
    [uu____16427]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16544 =
      let uu____16545 =
        let uu____16552 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty
           in
        let uu____16553 = varops.mk_unique "typing_range_const"  in
        (uu____16552, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16553)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16545  in
    [uu____16544]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____16587 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16587 x1 t  in
      let uu____16588 =
        let uu____16599 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16599)  in
      FStar_SMTEncoding_Util.mkForall uu____16588  in
    let uu____16622 =
      let uu____16623 =
        let uu____16630 =
          let uu____16631 =
            let uu____16642 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16642)  in
          FStar_SMTEncoding_Util.mkForall uu____16631  in
        (uu____16630,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16623  in
    [uu____16622]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
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
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16966 =
            FStar_Util.find_opt
              (fun uu____16992  ->
                 match uu____16992 with
                 | (l,uu____17004) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16966 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17029,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____17068 = encode_function_type_as_formula t env  in
        match uu____17068 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let encode_free_var :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____17114 =
                ((let uu____17117 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____17117) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____17114
              then
                let uu____17124 = new_term_constant_and_tok_from_lid env lid
                   in
                match uu____17124 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17143 =
                        let uu____17144 = FStar_Syntax_Subst.compress t_norm
                           in
                        uu____17144.FStar_Syntax_Syntax.n  in
                      match uu____17143 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17150) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17180  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17185 -> []  in
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function"))
                       in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function"))
                       in
                    ([d; dd], env1)
              else
                (let uu____17199 = prims.is lid  in
                 if uu____17199
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17207 = prims.mk lid vname  in
                   match uu____17207 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17231 =
                      let uu____17242 = curried_arrow_formals_comp t_norm  in
                      match uu____17242 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17260 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17260
                            then
                              let uu____17261 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___147_17264 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___147_17264.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___147_17264.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___147_17264.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___147_17264.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___147_17264.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___147_17264.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___147_17264.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___147_17264.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___147_17264.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___147_17264.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___147_17264.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___147_17264.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___147_17264.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___147_17264.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___147_17264.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___147_17264.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___147_17264.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___147_17264.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___147_17264.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___147_17264.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___147_17264.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___147_17264.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___147_17264.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___147_17264.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___147_17264.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___147_17264.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___147_17264.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___147_17264.FStar_TypeChecker_Env.identifier_info)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17261
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17276 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17276)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17231 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17321 =
                          new_term_constant_and_tok_from_lid env lid  in
                        (match uu____17321 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17342 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___119_17384  ->
                                       match uu___119_17384 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17388 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17388 with
                                            | (uu____17409,(xxsym,uu____17411))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17429 =
                                                  let uu____17430 =
                                                    let uu____17437 =
                                                      let uu____17438 =
                                                        let uu____17449 =
                                                          let uu____17450 =
                                                            let uu____17455 =
                                                              let uu____17456
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17456
                                                               in
                                                            (vapp,
                                                              uu____17455)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17450
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17449)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17438
                                                       in
                                                    (uu____17437,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17430
                                                   in
                                                [uu____17429])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17475 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17475 with
                                            | (uu____17496,(xxsym,uu____17498))
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
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  }  in
                                                let tp_name =
                                                  mk_term_projector_name d f1
                                                   in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx])
                                                   in
                                                let uu____17521 =
                                                  let uu____17522 =
                                                    let uu____17529 =
                                                      let uu____17530 =
                                                        let uu____17541 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17541)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17530
                                                       in
                                                    (uu____17529,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17522
                                                   in
                                                [uu____17521])
                                       | uu____17558 -> []))
                                in
                             let uu____17559 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17559 with
                              | (vars,guards,env',decls1,uu____17586) ->
                                  let uu____17599 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17608 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17608, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17610 =
                                          encode_formula p env'  in
                                        (match uu____17610 with
                                         | (g,ds) ->
                                             let uu____17621 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17621,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17599 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17634 =
                                           let uu____17641 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17641)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17634
                                          in
                                       let uu____17650 =
                                         let vname_decl =
                                           let uu____17658 =
                                             let uu____17669 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17679  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17669,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17658
                                            in
                                         let uu____17688 =
                                           let env2 =
                                             let uu___148_17694 = env1  in
                                             {
                                               bindings =
                                                 (uu___148_17694.bindings);
                                               depth = (uu___148_17694.depth);
                                               tcenv = (uu___148_17694.tcenv);
                                               warn = (uu___148_17694.warn);
                                               cache = (uu___148_17694.cache);
                                               nolabels =
                                                 (uu___148_17694.nolabels);
                                               use_zfuel_name =
                                                 (uu___148_17694.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___148_17694.current_module_name)
                                             }  in
                                           let uu____17695 =
                                             let uu____17696 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17696
                                              in
                                           if uu____17695
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17688 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17711::uu____17712 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                      in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff
                                                      in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff]
                                                      in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)]
                                                      in
                                                   let guarded_tok_typing =
                                                     let uu____17752 =
                                                       let uu____17763 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17763)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17752
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17790 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17793 =
                                               match formals with
                                               | [] ->
                                                   let uu____17810 =
                                                     let uu____17811 =
                                                       let uu____17814 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_43  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_43)
                                                         uu____17814
                                                        in
                                                     push_free_var env1 lid
                                                       vname uu____17811
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17810)
                                               | uu____17819 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let vtok_fresh =
                                                     let uu____17826 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (vtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____17826
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17828 =
                                                       let uu____17835 =
                                                         let uu____17836 =
                                                           let uu____17847 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17847)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17836
                                                          in
                                                       (uu____17835,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17828
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       vtok_fresh;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17793 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17650 with
                                        | (decls2,env2) ->
                                            let uu____17890 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17898 =
                                                encode_term res_t1 env'  in
                                              match uu____17898 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17911 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17911, decls)
                                               in
                                            (match uu____17890 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17922 =
                                                     let uu____17929 =
                                                       let uu____17930 =
                                                         let uu____17941 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17941)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17930
                                                        in
                                                     (uu____17929,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17922
                                                    in
                                                 let freshness =
                                                   let uu____17957 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17957
                                                   then
                                                     let uu____17962 =
                                                       let uu____17963 =
                                                         let uu____17974 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17985 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17974,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17985)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17963
                                                        in
                                                     let uu____17988 =
                                                       let uu____17991 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17991]  in
                                                     uu____17962 ::
                                                       uu____17988
                                                   else []  in
                                                 let g =
                                                   let uu____17996 =
                                                     let uu____17999 =
                                                       let uu____18002 =
                                                         let uu____18005 =
                                                           let uu____18008 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____18008
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____18005
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____18002
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17999
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17996
                                                    in
                                                 (g, env2))))))))
  
let declare_top_level_let :
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
          let uu____18043 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____18043 with
          | FStar_Pervasives_Native.None  ->
              let uu____18080 = encode_free_var false env x t t_norm []  in
              (match uu____18080 with
               | (decls,env1) ->
                   let uu____18107 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18107 with
                    | (n1,x',uu____18134) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18155) ->
              ((n1, x1), [], env)
  
let encode_top_level_val :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t  in
            let uu____18215 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____18215 with
            | (decls,env1) ->
                let uu____18234 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18234
                then
                  let uu____18241 =
                    let uu____18244 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18244  in
                  (uu____18241, env1)
                else (decls, env1)
  
let encode_top_level_vals :
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
             (fun uu____18299  ->
                fun lb  ->
                  match uu____18299 with
                  | (decls,env1) ->
                      let uu____18319 =
                        let uu____18326 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18326
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18319 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18348 = FStar_Syntax_Util.head_and_args t  in
    match uu____18348 with
    | (hd1,args) ->
        let uu____18385 =
          let uu____18386 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18386.FStar_Syntax_Syntax.n  in
        (match uu____18385 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18390,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18409 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18434  ->
      fun quals  ->
        match uu____18434 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18510 = FStar_Util.first_N nbinders formals  in
              match uu____18510 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18591  ->
                         fun uu____18592  ->
                           match (uu____18591, uu____18592) with
                           | ((formal,uu____18610),(binder,uu____18612)) ->
                               let uu____18621 =
                                 let uu____18628 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18628)  in
                               FStar_Syntax_Syntax.NT uu____18621) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18636 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18667  ->
                              match uu____18667 with
                              | (x,i) ->
                                  let uu____18678 =
                                    let uu___149_18679 = x  in
                                    let uu____18680 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___149_18679.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___149_18679.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18680
                                    }  in
                                  (uu____18678, i)))
                       in
                    FStar_All.pipe_right uu____18636
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18698 =
                      let uu____18699 = FStar_Syntax_Subst.compress body  in
                      let uu____18700 =
                        let uu____18701 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18701
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18699
                        uu____18700
                       in
                    uu____18698 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18762 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18762
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___150_18765 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___150_18765.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___150_18765.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___150_18765.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___150_18765.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___150_18765.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___150_18765.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___150_18765.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___150_18765.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___150_18765.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___150_18765.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___150_18765.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___150_18765.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___150_18765.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___150_18765.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___150_18765.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___150_18765.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___150_18765.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___150_18765.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___150_18765.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___150_18765.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.type_of =
                         (uu___150_18765.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___150_18765.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___150_18765.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___150_18765.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___150_18765.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___150_18765.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___150_18765.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___150_18765.FStar_TypeChecker_Env.identifier_info)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18798 = FStar_Syntax_Util.abs_formals e  in
                match uu____18798 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18862::uu____18863 ->
                         let uu____18878 =
                           let uu____18879 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____18879.FStar_Syntax_Syntax.n  in
                         (match uu____18878 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18924 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18924 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18966 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18966
                                   then
                                     let uu____19001 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____19001 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19095  ->
                                                   fun uu____19096  ->
                                                     match (uu____19095,
                                                             uu____19096)
                                                     with
                                                     | ((x,uu____19114),
                                                        (b,uu____19116)) ->
                                                         let uu____19125 =
                                                           let uu____19132 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____19132)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19125)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____19134 =
                                            let uu____19155 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____19155)
                                             in
                                          (uu____19134, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19223 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____19223 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19312) ->
                              let uu____19317 =
                                let uu____19338 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19338  in
                              (uu____19317, true)
                          | uu____19403 when Prims.op_Negation norm1 ->
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
                          | uu____19405 ->
                              let uu____19406 =
                                let uu____19407 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19408 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19407
                                  uu____19408
                                 in
                              failwith uu____19406)
                     | uu____19433 ->
                         let uu____19434 =
                           let uu____19435 =
                             FStar_Syntax_Subst.compress t_norm1  in
                           uu____19435.FStar_Syntax_Syntax.n  in
                         (match uu____19434 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____19480 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____19480 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1  in
                                   let uu____19512 =
                                     eta_expand1 [] formals1 e tres  in
                                   (match uu____19512 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____19595 -> (([], e, [], t_norm1), false)))
                 in
              aux false t_norm  in
            (try
               let uu____19651 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19651
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19663 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19757  ->
                            fun lb  ->
                              match uu____19757 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19852 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19852
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19855 =
                                      let uu____19870 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19870
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19855 with
                                    | (tok,decl,env2) ->
                                        let uu____19916 =
                                          let uu____19929 =
                                            let uu____19940 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____19940, tok)  in
                                          uu____19929 :: toks  in
                                        (uu____19916, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19663 with
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
                        | uu____20123 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20131 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____20131 vars)
                            else
                              (let uu____20133 =
                                 let uu____20140 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____20140)  in
                               FStar_SMTEncoding_Util.mkApp uu____20133)
                         in
                      let uu____20149 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___120_20153  ->
                                 match uu___120_20153 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____20154 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____20160 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____20160)))
                         in
                      if uu____20149
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____20198;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____20200;
                                FStar_Syntax_Syntax.lbeff = uu____20201;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                  in
                               let uu____20264 =
                                 let uu____20271 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm]
                                    in
                                 match uu____20271 with
                                 | (tcenv',uu____20289,e_t) ->
                                     let uu____20295 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____20306 -> failwith "Impossible"
                                        in
                                     (match uu____20295 with
                                      | (e1,t_norm1) ->
                                          ((let uu___153_20322 = env1  in
                                            {
                                              bindings =
                                                (uu___153_20322.bindings);
                                              depth = (uu___153_20322.depth);
                                              tcenv = tcenv';
                                              warn = (uu___153_20322.warn);
                                              cache = (uu___153_20322.cache);
                                              nolabels =
                                                (uu___153_20322.nolabels);
                                              use_zfuel_name =
                                                (uu___153_20322.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___153_20322.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___153_20322.current_module_name)
                                            }), e1, t_norm1))
                                  in
                               (match uu____20264 with
                                | (env',e1,t_norm1) ->
                                    let uu____20332 =
                                      destruct_bound_function flid t_norm1 e1
                                       in
                                    (match uu____20332 with
                                     | ((binders,body,uu____20353,uu____20354),curry)
                                         ->
                                         ((let uu____20365 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding")
                                              in
                                           if uu____20365
                                           then
                                             let uu____20366 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders
                                                in
                                             let uu____20367 =
                                               FStar_Syntax_Print.term_to_string
                                                 body
                                                in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____20366 uu____20367
                                           else ());
                                          (let uu____20369 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env'
                                              in
                                           match uu____20369 with
                                           | (vars,guards,env'1,binder_decls,uu____20396)
                                               ->
                                               let body1 =
                                                 let uu____20410 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1
                                                    in
                                                 if uu____20410
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body  in
                                               let app =
                                                 mk_app1 curry f ftok vars
                                                  in
                                               let uu____20413 =
                                                 let uu____20422 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic)
                                                    in
                                                 if uu____20422
                                                 then
                                                   let uu____20433 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app
                                                      in
                                                   let uu____20434 =
                                                     encode_formula body1
                                                       env'1
                                                      in
                                                   (uu____20433, uu____20434)
                                                 else
                                                   (let uu____20444 =
                                                      encode_term body1 env'1
                                                       in
                                                    (app, uu____20444))
                                                  in
                                               (match uu____20413 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____20467 =
                                                        let uu____20474 =
                                                          let uu____20475 =
                                                            let uu____20486 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2)
                                                               in
                                                            ([[app1]], vars,
                                                              uu____20486)
                                                             in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____20475
                                                           in
                                                        let uu____20497 =
                                                          let uu____20500 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str
                                                             in
                                                          FStar_Pervasives_Native.Some
                                                            uu____20500
                                                           in
                                                        (uu____20474,
                                                          uu____20497,
                                                          (Prims.strcat
                                                             "equation_" f))
                                                         in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____20467
                                                       in
                                                    let uu____20503 =
                                                      let uu____20506 =
                                                        let uu____20509 =
                                                          let uu____20512 =
                                                            let uu____20515 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1
                                                               in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____20515
                                                             in
                                                          FStar_List.append
                                                            decls2
                                                            uu____20512
                                                           in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____20509
                                                         in
                                                      FStar_List.append
                                                        decls1 uu____20506
                                                       in
                                                    (uu____20503, env1))))))
                           | uu____20520 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____20555 = varops.fresh "fuel"  in
                             (uu____20555, FStar_SMTEncoding_Term.Fuel_sort)
                              in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel
                              in
                           let env0 = env1  in
                           let uu____20558 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____20646  ->
                                     fun uu____20647  ->
                                       match (uu____20646, uu____20647) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                              in
                                           let g =
                                             let uu____20795 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented"
                                                in
                                             varops.new_fvar uu____20795  in
                                           let gtok =
                                             let uu____20797 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token"
                                                in
                                             varops.new_fvar uu____20797  in
                                           let env3 =
                                             let uu____20799 =
                                               let uu____20802 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm])
                                                  in
                                               FStar_All.pipe_left
                                                 (fun _0_44  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_44) uu____20802
                                                in
                                             push_free_var env2 flid gtok
                                               uu____20799
                                              in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1))
                              in
                           match uu____20558 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks  in
                               let encode_one_binding env01 uu____20958
                                 t_norm uu____20960 =
                                 match (uu____20958, uu____20960) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____21004;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____21005;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____21033 =
                                       let uu____21040 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm]
                                          in
                                       match uu____21040 with
                                       | (tcenv',uu____21062,e_t) ->
                                           let uu____21068 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____21079 ->
                                                 failwith "Impossible"
                                              in
                                           (match uu____21068 with
                                            | (e1,t_norm1) ->
                                                ((let uu___154_21095 = env2
                                                     in
                                                  {
                                                    bindings =
                                                      (uu___154_21095.bindings);
                                                    depth =
                                                      (uu___154_21095.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___154_21095.warn);
                                                    cache =
                                                      (uu___154_21095.cache);
                                                    nolabels =
                                                      (uu___154_21095.nolabels);
                                                    use_zfuel_name =
                                                      (uu___154_21095.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___154_21095.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___154_21095.current_module_name)
                                                  }), e1, t_norm1))
                                        in
                                     (match uu____21033 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____21110 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding")
                                               in
                                            if uu____21110
                                            then
                                              let uu____21111 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn
                                                 in
                                              let uu____21112 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1
                                                 in
                                              let uu____21113 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1
                                                 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____21111 uu____21112
                                                uu____21113
                                            else ());
                                           (let uu____21115 =
                                              destruct_bound_function flid
                                                t_norm1 e1
                                               in
                                            match uu____21115 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____21152 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding")
                                                     in
                                                  if uu____21152
                                                  then
                                                    let uu____21153 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders
                                                       in
                                                    let uu____21154 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body
                                                       in
                                                    let uu____21155 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals
                                                       in
                                                    let uu____21156 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres
                                                       in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____21153 uu____21154
                                                      uu____21155 uu____21156
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____21160 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env'
                                                     in
                                                  match uu____21160 with
                                                  | (vars,guards,env'1,binder_decls,uu____21191)
                                                      ->
                                                      let decl_g =
                                                        let uu____21205 =
                                                          let uu____21216 =
                                                            let uu____21219 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars
                                                               in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____21219
                                                             in
                                                          (g, uu____21216,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name"))
                                                           in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____21205
                                                         in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g
                                                         in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Token for fuel-instrumented partial applications"))
                                                         in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars
                                                         in
                                                      let app =
                                                        let uu____21244 =
                                                          let uu____21251 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars
                                                             in
                                                          (f, uu____21251)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21244
                                                         in
                                                      let gsapp =
                                                        let uu____21261 =
                                                          let uu____21268 =
                                                            let uu____21271 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm])
                                                               in
                                                            uu____21271 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____21268)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21261
                                                         in
                                                      let gmax =
                                                        let uu____21277 =
                                                          let uu____21284 =
                                                            let uu____21287 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  [])
                                                               in
                                                            uu____21287 ::
                                                              vars_tm
                                                             in
                                                          (g, uu____21284)
                                                           in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____21277
                                                         in
                                                      let body1 =
                                                        let uu____21293 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1
                                                           in
                                                        if uu____21293
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body  in
                                                      let uu____21295 =
                                                        encode_term body1
                                                          env'1
                                                         in
                                                      (match uu____21295 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____21313
                                                               =
                                                               let uu____21320
                                                                 =
                                                                 let uu____21321
                                                                   =
                                                                   let uu____21336
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                     in
                                                                   ([[gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____21336)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____21321
                                                                  in
                                                               let uu____21357
                                                                 =
                                                                 let uu____21360
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str
                                                                    in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____21360
                                                                  in
                                                               (uu____21320,
                                                                 uu____21357,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21313
                                                              in
                                                           let eqn_f =
                                                             let uu____21364
                                                               =
                                                               let uu____21371
                                                                 =
                                                                 let uu____21372
                                                                   =
                                                                   let uu____21383
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)  in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____21383)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21372
                                                                  in
                                                               (uu____21371,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21364
                                                              in
                                                           let eqn_g' =
                                                             let uu____21397
                                                               =
                                                               let uu____21404
                                                                 =
                                                                 let uu____21405
                                                                   =
                                                                   let uu____21416
                                                                    =
                                                                    let uu____21417
                                                                    =
                                                                    let uu____21422
                                                                    =
                                                                    let uu____21423
                                                                    =
                                                                    let uu____21430
                                                                    =
                                                                    let uu____21433
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____21433
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____21430)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21423
                                                                     in
                                                                    (gsapp,
                                                                    uu____21422)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____21417
                                                                     in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____21416)
                                                                    in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____21405
                                                                  in
                                                               (uu____21404,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g))
                                                                in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____21397
                                                              in
                                                           let uu____21456 =
                                                             let uu____21465
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02
                                                                in
                                                             match uu____21465
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____21494)
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
                                                                    let uu____21519
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    mk_Apply
                                                                    uu____21519
                                                                    (fuel ::
                                                                    vars1)
                                                                     in
                                                                   let uu____21524
                                                                    =
                                                                    let uu____21531
                                                                    =
                                                                    let uu____21532
                                                                    =
                                                                    let uu____21543
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21543)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21532
                                                                     in
                                                                    (uu____21531,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                     in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21524
                                                                    in
                                                                 let uu____21564
                                                                   =
                                                                   let uu____21571
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp  in
                                                                   match uu____21571
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____21584
                                                                    =
                                                                    let uu____21587
                                                                    =
                                                                    let uu____21588
                                                                    =
                                                                    let uu____21595
                                                                    =
                                                                    let uu____21596
                                                                    =
                                                                    let uu____21607
                                                                    =
                                                                    let uu____21608
                                                                    =
                                                                    let uu____21613
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____21613,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21608
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21607)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21596
                                                                     in
                                                                    (uu____21595,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21588
                                                                     in
                                                                    [uu____21587]
                                                                     in
                                                                    (d3,
                                                                    uu____21584)
                                                                    in
                                                                 (match uu____21564
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
                                                           (match uu____21456
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
                               let uu____21678 =
                                 let uu____21691 =
                                   FStar_List.zip3 gtoks1 typs1 bindings  in
                                 FStar_List.fold_left
                                   (fun uu____21770  ->
                                      fun uu____21771  ->
                                        match (uu____21770, uu____21771) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____21926 =
                                              encode_one_binding env01 gtok
                                                ty lb
                                               in
                                            (match uu____21926 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____21691
                                  in
                               (match uu____21678 with
                                | (decls2,eqns,env01) ->
                                    let uu____21999 =
                                      let isDeclFun uu___121_22011 =
                                        match uu___121_22011 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____22012 -> true
                                        | uu____22023 -> false  in
                                      let uu____22024 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten
                                         in
                                      FStar_All.pipe_right uu____22024
                                        (FStar_List.partition isDeclFun)
                                       in
                                    (match uu____21999 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns  in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22075 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22075
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____22124 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22124 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22128 = encode_sigelt' env se  in
      match uu____22128 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22144 =
                  let uu____22145 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22145  in
                [uu____22144]
            | uu____22146 ->
                let uu____22147 =
                  let uu____22150 =
                    let uu____22151 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22151  in
                  uu____22150 :: g  in
                let uu____22152 =
                  let uu____22155 =
                    let uu____22156 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22156  in
                  [uu____22155]  in
                FStar_List.append uu____22147 uu____22152
             in
          (g1, env1)

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22169 =
          let uu____22170 = FStar_Syntax_Subst.compress t  in
          uu____22170.FStar_Syntax_Syntax.n  in
        match uu____22169 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____22174)) ->
            (FStar_Util.string_of_bytes bytes) = "opaque_to_smt"
        | uu____22179 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22184 =
          let uu____22185 = FStar_Syntax_Subst.compress t  in
          uu____22185.FStar_Syntax_Syntax.n  in
        match uu____22184 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (bytes,uu____22189)) ->
            (FStar_Util.string_of_bytes bytes) = "uninterpreted_by_smt"
        | uu____22194 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22199 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22204 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22207 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22210 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22225 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22229 =
            let uu____22230 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____22230 Prims.op_Negation  in
          if uu____22229
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22256 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____22276 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____22276 with
               | (aname,atok,env2) ->
                   let uu____22292 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____22292 with
                    | (formals,uu____22310) ->
                        let uu____22323 =
                          let uu____22328 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____22328 env2  in
                        (match uu____22323 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22340 =
                                 let uu____22341 =
                                   let uu____22352 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22368  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____22352,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____22341
                                  in
                               [uu____22340;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____22381 =
                               let aux uu____22433 uu____22434 =
                                 match (uu____22433, uu____22434) with
                                 | ((bv,uu____22486),(env3,acc_sorts,acc)) ->
                                     let uu____22524 = gen_term_var env3 bv
                                        in
                                     (match uu____22524 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____22381 with
                              | (uu____22596,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____22619 =
                                      let uu____22626 =
                                        let uu____22627 =
                                          let uu____22638 =
                                            let uu____22639 =
                                              let uu____22644 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____22644)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22639
                                             in
                                          ([[app]], xs_sorts, uu____22638)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22627
                                         in
                                      (uu____22626,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22619
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____22664 =
                                      let uu____22671 =
                                        let uu____22672 =
                                          let uu____22683 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____22683)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22672
                                         in
                                      (uu____22671,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22664
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____22702 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____22702 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22730,uu____22731)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22732 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____22732 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22749,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____22755 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___122_22759  ->
                      match uu___122_22759 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22760 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22765 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22766 -> false))
               in
            Prims.op_Negation uu____22755  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____22775 =
               let uu____22782 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____22782 env fv t quals  in
             match uu____22775 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____22797 =
                   let uu____22800 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____22800  in
                 (uu____22797, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22808 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____22808 with
           | (uu____22817,f1) ->
               let uu____22819 = encode_formula f1 env  in
               (match uu____22819 with
                | (f2,decls) ->
                    let g =
                      let uu____22833 =
                        let uu____22834 =
                          let uu____22841 =
                            let uu____22844 =
                              let uu____22845 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____22845
                               in
                            FStar_Pervasives_Native.Some uu____22844  in
                          let uu____22846 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____22841, uu____22846)  in
                        FStar_SMTEncoding_Util.mkAssume uu____22834  in
                      [uu____22833]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22852) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____22864 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22882 =
                       let uu____22885 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____22885.FStar_Syntax_Syntax.fv_name  in
                     uu____22882.FStar_Syntax_Syntax.v  in
                   let uu____22886 =
                     let uu____22887 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____22887  in
                   if uu____22886
                   then
                     let val_decl =
                       let uu___155_22915 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___155_22915.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___155_22915.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___155_22915.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____22920 = encode_sigelt' env1 val_decl  in
                     match uu____22920 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____22864 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22948,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22950;
                          FStar_Syntax_Syntax.lbtyp = uu____22951;
                          FStar_Syntax_Syntax.lbeff = uu____22952;
                          FStar_Syntax_Syntax.lbdef = uu____22953;_}::[]),uu____22954)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22973 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____22973 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23002 =
                   let uu____23005 =
                     let uu____23006 =
                       let uu____23013 =
                         let uu____23014 =
                           let uu____23025 =
                             let uu____23026 =
                               let uu____23031 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23031)  in
                             FStar_SMTEncoding_Util.mkEq uu____23026  in
                           ([[b2t_x]], [xx], uu____23025)  in
                         FStar_SMTEncoding_Util.mkForall uu____23014  in
                       (uu____23013,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23006  in
                   [uu____23005]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23002
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23064,uu____23065) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___123_23074  ->
                  match uu___123_23074 with
                  | FStar_Syntax_Syntax.Discriminator uu____23075 -> true
                  | uu____23076 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23079,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23090 =
                     let uu____23091 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23091.FStar_Ident.idText  in
                   uu____23090 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___124_23095  ->
                     match uu___124_23095 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23096 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23100) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_23117  ->
                  match uu___125_23117 with
                  | FStar_Syntax_Syntax.Projector uu____23118 -> true
                  | uu____23123 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23126 = try_lookup_free_var env l  in
          (match uu____23126 with
           | FStar_Pervasives_Native.Some uu____23133 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___156_23137 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___156_23137.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___156_23137.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___156_23137.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23144) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23162) ->
          let uu____23171 = encode_sigelts env ses  in
          (match uu____23171 with
           | (g,env1) ->
               let uu____23188 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___126_23211  ->
                         match uu___126_23211 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23212;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23213;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23214;_}
                             -> false
                         | uu____23217 -> true))
                  in
               (match uu____23188 with
                | (g',inversions) ->
                    let uu____23232 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___127_23253  ->
                              match uu___127_23253 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23254 ->
                                  true
                              | uu____23265 -> false))
                       in
                    (match uu____23232 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23283,tps,k,uu____23286,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___128_23303  ->
                    match uu___128_23303 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23304 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23313 = c  in
              match uu____23313 with
              | (name,args,uu____23318,uu____23319,uu____23320) ->
                  let uu____23325 =
                    let uu____23326 =
                      let uu____23337 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23354  ->
                                match uu____23354 with
                                | (uu____23361,sort,uu____23363) -> sort))
                         in
                      (name, uu____23337, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____23326  in
                  [uu____23325]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____23390 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23396 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____23396 FStar_Option.isNone))
               in
            if uu____23390
            then []
            else
              (let uu____23428 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____23428 with
               | (xxsym,xx) ->
                   let uu____23437 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23476  ->
                             fun l  ->
                               match uu____23476 with
                               | (out,decls) ->
                                   let uu____23496 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____23496 with
                                    | (uu____23507,data_t) ->
                                        let uu____23509 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____23509 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23555 =
                                                 let uu____23556 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____23556.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____23555 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23567,indices) ->
                                                   indices
                                               | uu____23589 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23613  ->
                                                         match uu____23613
                                                         with
                                                         | (x,uu____23619) ->
                                                             let uu____23620
                                                               =
                                                               let uu____23621
                                                                 =
                                                                 let uu____23628
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____23628,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23621
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____23620)
                                                    env)
                                                in
                                             let uu____23631 =
                                               encode_args indices env1  in
                                             (match uu____23631 with
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
                                                      let uu____23657 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23673
                                                                 =
                                                                 let uu____23678
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23678,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23673)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23657
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23681 =
                                                      let uu____23682 =
                                                        let uu____23687 =
                                                          let uu____23688 =
                                                            let uu____23693 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23693,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23688
                                                           in
                                                        (out, uu____23687)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23682
                                                       in
                                                    (uu____23681,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____23437 with
                    | (data_ax,decls) ->
                        let uu____23706 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23706 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23717 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23717 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23721 =
                                 let uu____23728 =
                                   let uu____23729 =
                                     let uu____23740 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23755 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23740,
                                       uu____23755)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23729
                                    in
                                 let uu____23770 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23728,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23770)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23721
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23773 =
            let uu____23786 =
              let uu____23787 = FStar_Syntax_Subst.compress k  in
              uu____23787.FStar_Syntax_Syntax.n  in
            match uu____23786 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23832 -> (tps, k)  in
          (match uu____23773 with
           | (formals,res) ->
               let uu____23855 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23855 with
                | (formals1,res1) ->
                    let uu____23866 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23866 with
                     | (vars,guards,env',binder_decls,uu____23891) ->
                         let uu____23904 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____23904 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____23923 =
                                  let uu____23930 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____23930)  in
                                FStar_SMTEncoding_Util.mkApp uu____23923  in
                              let uu____23939 =
                                let tname_decl =
                                  let uu____23949 =
                                    let uu____23950 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23982  ->
                                              match uu____23982 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____23995 = varops.next_id ()  in
                                    (tname, uu____23950,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23995, false)
                                     in
                                  constructor_or_logic_type_decl uu____23949
                                   in
                                let uu____24004 =
                                  match vars with
                                  | [] ->
                                      let uu____24017 =
                                        let uu____24018 =
                                          let uu____24021 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_45  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_45) uu____24021
                                           in
                                        push_free_var env1 t tname
                                          uu____24018
                                         in
                                      ([], uu____24017)
                                  | uu____24028 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24037 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24037
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24051 =
                                          let uu____24058 =
                                            let uu____24059 =
                                              let uu____24074 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24074)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24059
                                             in
                                          (uu____24058,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24051
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24004 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____23939 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24114 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24114 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24132 =
                                               let uu____24133 =
                                                 let uu____24140 =
                                                   let uu____24141 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24141
                                                    in
                                                 (uu____24140,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24133
                                                in
                                             [uu____24132]
                                           else []  in
                                         let uu____24145 =
                                           let uu____24148 =
                                             let uu____24151 =
                                               let uu____24152 =
                                                 let uu____24159 =
                                                   let uu____24160 =
                                                     let uu____24171 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24171)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24160
                                                    in
                                                 (uu____24159,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24152
                                                in
                                             [uu____24151]  in
                                           FStar_List.append karr uu____24148
                                            in
                                         FStar_List.append decls1 uu____24145
                                      in
                                   let aux =
                                     let uu____24187 =
                                       let uu____24190 =
                                         inversion_axioms tapp vars  in
                                       let uu____24193 =
                                         let uu____24196 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24196]  in
                                       FStar_List.append uu____24190
                                         uu____24193
                                        in
                                     FStar_List.append kindingAx uu____24187
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24203,uu____24204,uu____24205,uu____24206,uu____24207)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24215,t,uu____24217,n_tps,uu____24219) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24227 = new_term_constant_and_tok_from_lid env d  in
          (match uu____24227 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____24244 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____24244 with
                | (formals,t_res) ->
                    let uu____24279 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24279 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____24293 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____24293 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____24363 =
                                            mk_term_projector_name d x  in
                                          (uu____24363,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____24365 =
                                  let uu____24384 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24384, true)
                                   in
                                FStar_All.pipe_right uu____24365
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
                              let uu____24423 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____24423 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24435::uu____24436 ->
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
                                         let uu____24481 =
                                           let uu____24492 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24492)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24481
                                     | uu____24517 -> tok_typing  in
                                   let uu____24526 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____24526 with
                                    | (vars',guards',env'',decls_formals,uu____24551)
                                        ->
                                        let uu____24564 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1
                                           in
                                        (match uu____24564 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24595 ->
                                                   let uu____24602 =
                                                     let uu____24603 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24603
                                                      in
                                                   [uu____24602]
                                                in
                                             let encode_elim uu____24613 =
                                               let uu____24614 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____24614 with
                                               | (head1,args) ->
                                                   let uu____24657 =
                                                     let uu____24658 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24658.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24657 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24668;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24669;_},uu____24670)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____24676 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____24676
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
                                                                 | uu____24719
                                                                    ->
                                                                    let uu____24720
                                                                    =
                                                                    let uu____24721
                                                                    =
                                                                    let uu____24726
                                                                    =
                                                                    let uu____24727
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24727
                                                                     in
                                                                    (uu____24726,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos))
                                                                     in
                                                                    FStar_Errors.Error
                                                                    uu____24721
                                                                     in
                                                                    FStar_Exn.raise
                                                                    uu____24720
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24743
                                                                    =
                                                                    let uu____24744
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24744
                                                                     in
                                                                    if
                                                                    uu____24743
                                                                    then
                                                                    let uu____24757
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24757]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____24759
                                                               =
                                                               let uu____24772
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24822
                                                                     ->
                                                                    fun
                                                                    uu____24823
                                                                     ->
                                                                    match 
                                                                    (uu____24822,
                                                                    uu____24823)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24918
                                                                    =
                                                                    let uu____24925
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24925
                                                                     in
                                                                    (match uu____24918
                                                                    with
                                                                    | 
                                                                    (uu____24938,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24946
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24946
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24948
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24948
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
                                                                 uu____24772
                                                                in
                                                             (match uu____24759
                                                              with
                                                              | (uu____24963,arg_vars,elim_eqns_or_guards,uu____24966)
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
                                                                    (FStar_Pervasives_Native.Some
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
                                                                    let uu____24996
                                                                    =
                                                                    let uu____25003
                                                                    =
                                                                    let uu____25004
                                                                    =
                                                                    let uu____25015
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25026
                                                                    =
                                                                    let uu____25027
                                                                    =
                                                                    let uu____25032
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25032)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25027
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25015,
                                                                    uu____25026)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25004
                                                                     in
                                                                    (uu____25003,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24996
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25055
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25055,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25057
                                                                    =
                                                                    let uu____25064
                                                                    =
                                                                    let uu____25065
                                                                    =
                                                                    let uu____25076
                                                                    =
                                                                    let uu____25081
                                                                    =
                                                                    let uu____25084
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25084]
                                                                     in
                                                                    [uu____25081]
                                                                     in
                                                                    let uu____25089
                                                                    =
                                                                    let uu____25090
                                                                    =
                                                                    let uu____25095
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25096
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25095,
                                                                    uu____25096)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25090
                                                                     in
                                                                    (uu____25076,
                                                                    [x],
                                                                    uu____25089)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25065
                                                                     in
                                                                    let uu____25115
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25064,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25115)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25057
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25122
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
                                                                    (let uu____25150
                                                                    =
                                                                    let uu____25151
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25151
                                                                    dapp1  in
                                                                    [uu____25150])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25122
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25158
                                                                    =
                                                                    let uu____25165
                                                                    =
                                                                    let uu____25166
                                                                    =
                                                                    let uu____25177
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25188
                                                                    =
                                                                    let uu____25189
                                                                    =
                                                                    let uu____25194
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25194)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25189
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25177,
                                                                    uu____25188)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25166
                                                                     in
                                                                    (uu____25165,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25158)
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
                                                        let uu____25215 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____25215
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
                                                                 | uu____25258
                                                                    ->
                                                                    let uu____25259
                                                                    =
                                                                    let uu____25260
                                                                    =
                                                                    let uu____25265
                                                                    =
                                                                    let uu____25266
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25266
                                                                     in
                                                                    (uu____25265,
                                                                    (orig_arg.FStar_Syntax_Syntax.pos))
                                                                     in
                                                                    FStar_Errors.Error
                                                                    uu____25260
                                                                     in
                                                                    FStar_Exn.raise
                                                                    uu____25259
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25282
                                                                    =
                                                                    let uu____25283
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25283
                                                                     in
                                                                    if
                                                                    uu____25282
                                                                    then
                                                                    let uu____25296
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25296]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____25298
                                                               =
                                                               let uu____25311
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25361
                                                                     ->
                                                                    fun
                                                                    uu____25362
                                                                     ->
                                                                    match 
                                                                    (uu____25361,
                                                                    uu____25362)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25457
                                                                    =
                                                                    let uu____25464
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25464
                                                                     in
                                                                    (match uu____25457
                                                                    with
                                                                    | 
                                                                    (uu____25477,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25485
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25485
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25487
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25487
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
                                                                 uu____25311
                                                                in
                                                             (match uu____25298
                                                              with
                                                              | (uu____25502,arg_vars,elim_eqns_or_guards,uu____25505)
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
                                                                    (FStar_Pervasives_Native.Some
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
                                                                    let uu____25535
                                                                    =
                                                                    let uu____25542
                                                                    =
                                                                    let uu____25543
                                                                    =
                                                                    let uu____25554
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25565
                                                                    =
                                                                    let uu____25566
                                                                    =
                                                                    let uu____25571
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25571)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25566
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25554,
                                                                    uu____25565)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25543
                                                                     in
                                                                    (uu____25542,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25535
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25594
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25594,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25596
                                                                    =
                                                                    let uu____25603
                                                                    =
                                                                    let uu____25604
                                                                    =
                                                                    let uu____25615
                                                                    =
                                                                    let uu____25620
                                                                    =
                                                                    let uu____25623
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25623]
                                                                     in
                                                                    [uu____25620]
                                                                     in
                                                                    let uu____25628
                                                                    =
                                                                    let uu____25629
                                                                    =
                                                                    let uu____25634
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25635
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25634,
                                                                    uu____25635)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25629
                                                                     in
                                                                    (uu____25615,
                                                                    [x],
                                                                    uu____25628)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25604
                                                                     in
                                                                    let uu____25654
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25603,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25654)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25596
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25661
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
                                                                    (let uu____25689
                                                                    =
                                                                    let uu____25690
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25690
                                                                    dapp1  in
                                                                    [uu____25689])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25661
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25697
                                                                    =
                                                                    let uu____25704
                                                                    =
                                                                    let uu____25705
                                                                    =
                                                                    let uu____25716
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25727
                                                                    =
                                                                    let uu____25728
                                                                    =
                                                                    let uu____25733
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25733)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25728
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25716,
                                                                    uu____25727)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25705
                                                                     in
                                                                    (uu____25704,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25697)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25752 ->
                                                        ((let uu____25754 =
                                                            let uu____25755 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d
                                                               in
                                                            let uu____25756 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1
                                                               in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____25755
                                                              uu____25756
                                                             in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25754);
                                                         ([], [])))
                                                in
                                             let uu____25761 = encode_elim ()
                                                in
                                             (match uu____25761 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25781 =
                                                      let uu____25784 =
                                                        let uu____25787 =
                                                          let uu____25790 =
                                                            let uu____25793 =
                                                              let uu____25794
                                                                =
                                                                let uu____25805
                                                                  =
                                                                  let uu____25808
                                                                    =
                                                                    let uu____25809
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25809
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25808
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25805)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25794
                                                               in
                                                            [uu____25793]  in
                                                          let uu____25814 =
                                                            let uu____25817 =
                                                              let uu____25820
                                                                =
                                                                let uu____25823
                                                                  =
                                                                  let uu____25826
                                                                    =
                                                                    let uu____25829
                                                                    =
                                                                    let uu____25832
                                                                    =
                                                                    let uu____25833
                                                                    =
                                                                    let uu____25840
                                                                    =
                                                                    let uu____25841
                                                                    =
                                                                    let uu____25852
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25852)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25841
                                                                     in
                                                                    (uu____25840,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25833
                                                                     in
                                                                    let uu____25865
                                                                    =
                                                                    let uu____25868
                                                                    =
                                                                    let uu____25869
                                                                    =
                                                                    let uu____25876
                                                                    =
                                                                    let uu____25877
                                                                    =
                                                                    let uu____25888
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25899
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25888,
                                                                    uu____25899)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25877
                                                                     in
                                                                    (uu____25876,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25869
                                                                     in
                                                                    [uu____25868]
                                                                     in
                                                                    uu____25832
                                                                    ::
                                                                    uu____25865
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25829
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25826
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25823
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25820
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25817
                                                             in
                                                          FStar_List.append
                                                            uu____25790
                                                            uu____25814
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25787
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25784
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25781
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____25945  ->
              fun se  ->
                match uu____25945 with
                | (g,env1) ->
                    let uu____25965 = encode_sigelt env1 se  in
                    (match uu____25965 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26024 =
        match uu____26024 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26056 ->
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
                 ((let uu____26062 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26062
                   then
                     let uu____26063 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26064 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26065 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26063 uu____26064 uu____26065
                   else ());
                  (let uu____26067 = encode_term t1 env1  in
                   match uu____26067 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____26083 =
                         let uu____26090 =
                           let uu____26091 =
                             let uu____26092 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____26092
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____26091  in
                         new_term_constant_from_string env1 x uu____26090  in
                       (match uu____26083 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____26108 = FStar_Options.log_queries ()
                                 in
                              if uu____26108
                              then
                                let uu____26111 =
                                  let uu____26112 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____26113 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____26114 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26112 uu____26113 uu____26114
                                   in
                                FStar_Pervasives_Native.Some uu____26111
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26130,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26144 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26144 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26167,se,uu____26169) ->
                 let uu____26174 = encode_sigelt env1 se  in
                 (match uu____26174 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26191,se) ->
                 let uu____26197 = encode_sigelt env1 se  in
                 (match uu____26197 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26214 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26214 with | (uu____26237,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26252 'Auu____26253 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26253,'Auu____26252)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26321  ->
              match uu____26321 with
              | (l,uu____26333,uu____26334) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26380  ->
              match uu____26380 with
              | (l,uu____26394,uu____26395) ->
                  let uu____26404 =
                    FStar_All.pipe_left
                      (fun _0_46  -> FStar_SMTEncoding_Term.Echo _0_46)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____26405 =
                    let uu____26408 =
                      let uu____26409 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____26409  in
                    [uu____26408]  in
                  uu____26404 :: uu____26405))
       in
    (prefix1, suffix)
  
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26431 =
      let uu____26434 =
        let uu____26435 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____26438 =
          let uu____26439 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____26439 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26435;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26438
        }  in
      [uu____26434]  in
    FStar_ST.op_Colon_Equals last_env uu____26431
  
let get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26466 = FStar_ST.op_Bang last_env  in
      match uu____26466 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26488 ->
          let uu___157_26491 = e  in
          let uu____26492 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___157_26491.bindings);
            depth = (uu___157_26491.depth);
            tcenv;
            warn = (uu___157_26491.warn);
            cache = (uu___157_26491.cache);
            nolabels = (uu___157_26491.nolabels);
            use_zfuel_name = (uu___157_26491.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___157_26491.encode_non_total_function_typ);
            current_module_name = uu____26492
          }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____26497 = FStar_ST.op_Bang last_env  in
    match uu____26497 with
    | [] -> failwith "Empty env stack"
    | uu____26518::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____26543  ->
    let uu____26544 = FStar_ST.op_Bang last_env  in
    match uu____26544 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___158_26573 = hd1  in
          {
            bindings = (uu___158_26573.bindings);
            depth = (uu___158_26573.depth);
            tcenv = (uu___158_26573.tcenv);
            warn = (uu___158_26573.warn);
            cache = refs;
            nolabels = (uu___158_26573.nolabels);
            use_zfuel_name = (uu___158_26573.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_26573.encode_non_total_function_typ);
            current_module_name = (uu___158_26573.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____26595  ->
    let uu____26596 = FStar_ST.op_Bang last_env  in
    match uu____26596 with
    | [] -> failwith "Popping an empty stack"
    | uu____26617::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let mark_env : Prims.unit -> Prims.unit = fun uu____26642  -> push_env () 
let reset_mark_env : Prims.unit -> Prims.unit =
  fun uu____26646  -> pop_env () 
let commit_mark_env : Prims.unit -> Prims.unit =
  fun uu____26650  ->
    let uu____26651 = FStar_ST.op_Bang last_env  in
    match uu____26651 with
    | hd1::uu____26673::tl1 -> FStar_ST.op_Colon_Equals last_env (hd1 :: tl1)
    | uu____26695 -> failwith "Impossible"
  
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
        | (uu____26760::uu____26761,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___159_26769 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___159_26769.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___159_26769.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___159_26769.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26770 -> d
  
let fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____26787 =
        let uu____26790 =
          let uu____26791 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26791  in
        let uu____26792 = open_fact_db_tags env  in uu____26790 ::
          uu____26792
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26787
  
let encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____26816 = encode_sigelt env se  in
      match uu____26816 with
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
        let uu____26854 = FStar_Options.log_queries ()  in
        if uu____26854
        then
          let uu____26857 =
            let uu____26858 =
              let uu____26859 =
                let uu____26860 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26860 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26859  in
            FStar_SMTEncoding_Term.Caption uu____26858  in
          uu____26857 :: decls
        else decls  in
      let env =
        let uu____26871 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____26871 tcenv  in
      let uu____26872 = encode_top_level_facts env se  in
      match uu____26872 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____26886 = caption decls  in
            FStar_SMTEncoding_Z3.giveZ3 uu____26886))
  
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
      (let uu____26900 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26900
       then
         let uu____26901 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26901
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26936  ->
                 fun se  ->
                   match uu____26936 with
                   | (g,env2) ->
                       let uu____26956 = encode_top_level_facts env2 se  in
                       (match uu____26956 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26979 =
         encode_signature
           (let uu___160_26988 = env  in
            {
              bindings = (uu___160_26988.bindings);
              depth = (uu___160_26988.depth);
              tcenv = (uu___160_26988.tcenv);
              warn = false;
              cache = (uu___160_26988.cache);
              nolabels = (uu___160_26988.nolabels);
              use_zfuel_name = (uu___160_26988.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___160_26988.encode_non_total_function_typ);
              current_module_name = (uu___160_26988.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26979 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27005 = FStar_Options.log_queries ()  in
             if uu____27005
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___161_27013 = env1  in
               {
                 bindings = (uu___161_27013.bindings);
                 depth = (uu___161_27013.depth);
                 tcenv = (uu___161_27013.tcenv);
                 warn = true;
                 cache = (uu___161_27013.cache);
                 nolabels = (uu___161_27013.nolabels);
                 use_zfuel_name = (uu___161_27013.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___161_27013.encode_non_total_function_typ);
                 current_module_name = (uu___161_27013.current_module_name)
               });
            (let uu____27015 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____27015
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let encode_query :
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
        (let uu____27070 =
           let uu____27071 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____27071.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27070);
        (let env =
           let uu____27073 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____27073 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____27085 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27120 = aux rest  in
                 (match uu____27120 with
                  | (out,rest1) ->
                      let t =
                        let uu____27150 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____27150 with
                        | FStar_Pervasives_Native.Some uu____27155 ->
                            let uu____27156 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____27156
                              x.FStar_Syntax_Syntax.sort
                        | uu____27157 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____27161 =
                        let uu____27164 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___162_27167 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___162_27167.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___162_27167.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____27164 :: out  in
                      (uu____27161, rest1))
             | uu____27172 -> ([], bindings1)  in
           let uu____27179 = aux bindings  in
           match uu____27179 with
           | (closing,bindings1) ->
               let uu____27204 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____27204, bindings1)
            in
         match uu____27085 with
         | (q1,bindings1) ->
             let uu____27227 =
               let uu____27232 =
                 FStar_List.filter
                   (fun uu___129_27237  ->
                      match uu___129_27237 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27238 ->
                          false
                      | uu____27245 -> true) bindings1
                  in
               encode_env_bindings env uu____27232  in
             (match uu____27227 with
              | (env_decls,env1) ->
                  ((let uu____27263 =
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
                    if uu____27263
                    then
                      let uu____27264 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27264
                    else ());
                   (let uu____27266 = encode_formula q1 env1  in
                    match uu____27266 with
                    | (phi,qdecls) ->
                        let uu____27287 =
                          let uu____27292 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27292 phi
                           in
                        (match uu____27287 with
                         | (labels,phi1) ->
                             let uu____27309 = encode_labels labels  in
                             (match uu____27309 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____27346 =
                                      let uu____27353 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____27354 =
                                        varops.mk_unique "@query"  in
                                      (uu____27353,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27354)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27346
                                     in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"]
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  
let is_trivial :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____27373 = FStar_TypeChecker_Env.current_module tcenv  in
        get_env uu____27373 tcenv  in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____27375 = encode_formula q env  in
       match uu____27375 with
       | (f,uu____27381) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____27383) -> true
             | uu____27388 -> false)))
  