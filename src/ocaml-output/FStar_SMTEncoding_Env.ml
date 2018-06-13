open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____6 -> false
  
let add_fuel :
  'Auu____13 . 'Auu____13 -> 'Auu____13 Prims.list -> 'Auu____13 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____30 = FStar_Options.unthrottle_inductives ()  in
      if uu____30 then tl1 else x :: tl1
  
let withenv :
  'Auu____44 'Auu____45 'Auu____46 .
    'Auu____44 ->
      ('Auu____45,'Auu____46) FStar_Pervasives_Native.tuple2 ->
        ('Auu____45,'Auu____46,'Auu____44) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____66  -> match uu____66 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____81 'Auu____82 'Auu____83 .
    (('Auu____81,'Auu____82) FStar_Util.either,'Auu____83)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____81,'Auu____82) FStar_Util.either,'Auu____83)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___354_130  ->
         match uu___354_130 with
         | (FStar_Util.Inl uu____139,uu____140) -> false
         | uu____145 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___356_172 = a  in
        let uu____173 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____173;
          FStar_Syntax_Syntax.index =
            (uu___356_172.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___356_172.FStar_Syntax_Syntax.sort)
        }  in
      let uu____174 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____174
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____195 =
          let uu____196 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____196  in
        let uu____197 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____197 with
        | (uu____202,t) ->
            let uu____204 =
              let uu____205 = FStar_Syntax_Subst.compress t  in
              uu____205.FStar_Syntax_Syntax.n  in
            (match uu____204 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____226 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____226 with
                  | (binders,uu____232) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____247 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____258 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____258
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____269 =
        let uu____274 = mk_term_projector_name lid a  in
        (uu____274,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____269
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____285 =
        let uu____290 = mk_term_projector_name_by_pos lid i  in
        (uu____290,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____285
  
let mk_data_tester :
  'Auu____299 .
    'Auu____299 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
  
type varops_t =
  {
  push: unit -> unit ;
  pop: unit -> unit ;
  snapshot: unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2 ;
  rollback: Prims.int FStar_Pervasives_Native.option -> unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }
let (__proj__Mkvarops_t__item__push : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__pop
  
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int,unit) FStar_Pervasives_Native.tuple2) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__snapshot
  
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__rollback
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop;
        snapshot = __fname__snapshot; rollback = __fname__rollback;
        new_var = __fname__new_var; new_fvar = __fname__new_fvar;
        fresh = __fname__fresh; string_const = __fname__string_const;
        next_id = __fname__next_id; mk_unique = __fname__mk_unique;_} ->
        __fname__mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____1072 =
    let uu____1073 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____1076 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____1073, uu____1076)  in
  let scopes =
    let uu____1096 = let uu____1107 = new_scope ()  in [uu____1107]  in
    FStar_Util.mk_ref uu____1096  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1150 =
        let uu____1153 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1153
          (fun uu____1240  ->
             match uu____1240 with
             | (names1,uu____1252) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1150 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1261 ->
          (FStar_Util.incr ctr;
           (let uu____1296 =
              let uu____1297 =
                let uu____1298 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1298  in
              Prims.strcat "__" uu____1297  in
            Prims.strcat y1 uu____1296))
       in
    let top_scope =
      let uu____1347 =
        let uu____1356 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1356
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1347  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1477 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1563 =
      let uu____1564 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1564  in
    FStar_Util.format2 "%s_%s" pfx uu____1563  in
  let string_const s =
    let uu____1571 =
      let uu____1574 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1574
        (fun uu____1661  ->
           match uu____1661 with
           | (uu____1672,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1571 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1685 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1685  in
        let top_scope =
          let uu____1689 =
            let uu____1698 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1698  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1689  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1802 =
    let uu____1803 =
      let uu____1814 = new_scope ()  in
      let uu____1823 = FStar_ST.op_Bang scopes  in uu____1814 :: uu____1823
       in
    FStar_ST.op_Colon_Equals scopes uu____1803  in
  let pop1 uu____1977 =
    let uu____1978 =
      let uu____1989 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1989
       in
    FStar_ST.op_Colon_Equals scopes uu____1978  in
  let snapshot1 uu____2147 = FStar_Common.snapshot push1 scopes ()  in
  let rollback1 depth = FStar_Common.rollback pop1 scopes depth  in
  {
    push = push1;
    pop = pop1;
    snapshot = snapshot1;
    rollback = rollback1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  } 
let (unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv) =
  fun x  ->
    let uu___357_2223 = x  in
    let uu____2224 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____2224;
      FStar_Syntax_Syntax.index = (uu___357_2223.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___357_2223.FStar_Syntax_Syntax.sort)
    }
  
type fvar_binding =
  {
  fvar_lid: FStar_Ident.lident ;
  smt_arity: Prims.int ;
  smt_id: Prims.string ;
  smt_token: FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  smt_fuel_partial_app:
    FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option }
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__fvar_lid
  
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_arity
  
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_id
  
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_token
  
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid = __fname__fvar_lid; smt_arity = __fname__smt_arity;
        smt_id = __fname__smt_id; smt_token = __fname__smt_token;
        smt_fuel_partial_app = __fname__smt_fuel_partial_app;_} ->
        __fname__smt_fuel_partial_app
  
let binder_of_eithervar :
  'Auu____2338 'Auu____2339 .
    'Auu____2338 ->
      ('Auu____2338,'Auu____2339 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }
let (__proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
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
  bvar_bindings:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2 FStar_Util.pimap FStar_Util.psmap
    ;
  fvar_bindings: fvar_binding FStar_Util.psmap ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string ;
  encoding_quantifier: Prims.bool }
let (__proj__Mkenv_t__item__bvar_bindings :
  env_t ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2 FStar_Util.pimap FStar_Util.psmap)
  =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__bvar_bindings
  
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t -> fvar_binding FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__fvar_bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__warn
  
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__cache
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__current_module_name
  
let (__proj__Mkenv_t__item__encoding_quantifier : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings = __fname__bvar_bindings;
        fvar_bindings = __fname__fvar_bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;
        encoding_quantifier = __fname__encoding_quantifier;_} ->
        __fname__encoding_quantifier
  
let mk_cache_entry :
  'Auu____2860 .
    'Auu____2860 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls1  ->
          let names1 =
            FStar_All.pipe_right t_decls1
              (FStar_List.collect
                 (fun uu___355_2898  ->
                    match uu___355_2898 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2902 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls1;
            cache_symbol_assumption_names = names1
          }
  
let (use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let (print_env : env_t -> Prims.string) =
  fun e  ->
    let bvars =
      FStar_Util.psmap_fold e.bvar_bindings
        (fun _k  ->
           fun pi  ->
             fun acc  ->
               FStar_Util.pimap_fold pi
                 (fun _i  ->
                    fun uu____2953  ->
                      fun acc1  ->
                        match uu____2953 with
                        | (x,_term) ->
                            let uu____2965 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____2965 :: acc1) acc) []
       in
    let allvars =
      FStar_Util.psmap_fold e.fvar_bindings
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____2981 ->
          let uu____2984 = FStar_Syntax_Print.lid_to_string l  in
          Prims.strcat "...," uu____2984
       in
    FStar_String.concat ", " (last_fvar :: bvars)
  
let (lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      let uu____3001 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3001 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      FStar_Util.psmap_try_find env.fvar_bindings lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3067 .
    (FStar_Syntax_Syntax.bv,'Auu____3067) FStar_Pervasives_Native.tuple2 ->
      (FStar_Syntax_Syntax.bv,'Auu____3067) FStar_Pervasives_Native.tuple2
        FStar_Util.pimap FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv,'Auu____3067) FStar_Pervasives_Native.tuple2
          FStar_Util.pimap FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3127 =
             let uu____3134 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3134 pimap_opt  in
           FStar_Util.pimap_add uu____3127
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    fvar_binding FStar_Util.psmap -> fvar_binding FStar_Util.psmap)
  =
  fun fvb  ->
    fun fvbs  -> FStar_Util.psmap_add fvbs (fvb.fvar_lid).FStar_Ident.str fvb
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____3186 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____3186)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      let uu____3205 =
        let uu___358_3206 = env  in
        let uu____3207 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3207;
          fvar_bindings = (uu___358_3206.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___358_3206.tcenv);
          warn = (uu___358_3206.warn);
          cache = (uu___358_3206.cache);
          nolabels = (uu___358_3206.nolabels);
          use_zfuel_name = (uu___358_3206.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___358_3206.encode_non_total_function_typ);
          current_module_name = (uu___358_3206.current_module_name);
          encoding_quantifier = (uu___358_3206.encoding_quantifier)
        }  in
      (ysym, y, uu____3205)
  
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      let uu____3236 =
        let uu___359_3237 = env  in
        let uu____3238 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3238;
          fvar_bindings = (uu___359_3237.fvar_bindings);
          depth = (uu___359_3237.depth);
          tcenv = (uu___359_3237.tcenv);
          warn = (uu___359_3237.warn);
          cache = (uu___359_3237.cache);
          nolabels = (uu___359_3237.nolabels);
          use_zfuel_name = (uu___359_3237.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___359_3237.encode_non_total_function_typ);
          current_module_name = (uu___359_3237.current_module_name);
          encoding_quantifier = (uu___359_3237.encoding_quantifier)
        }  in
      (ysym, y, uu____3236)
  
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        let uu____3272 =
          let uu___360_3273 = env  in
          let uu____3274 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3274;
            fvar_bindings = (uu___360_3273.fvar_bindings);
            depth = (uu___360_3273.depth);
            tcenv = (uu___360_3273.tcenv);
            warn = (uu___360_3273.warn);
            cache = (uu___360_3273.cache);
            nolabels = (uu___360_3273.nolabels);
            use_zfuel_name = (uu___360_3273.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___360_3273.encode_non_total_function_typ);
            current_module_name = (uu___360_3273.current_module_name);
            encoding_quantifier = (uu___360_3273.encoding_quantifier)
          }  in
        (ysym, y, uu____3272)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___361_3298 = env  in
        let uu____3299 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3299;
          fvar_bindings = (uu___361_3298.fvar_bindings);
          depth = (uu___361_3298.depth);
          tcenv = (uu___361_3298.tcenv);
          warn = (uu___361_3298.warn);
          cache = (uu___361_3298.cache);
          nolabels = (uu___361_3298.nolabels);
          use_zfuel_name = (uu___361_3298.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___361_3298.encode_non_total_function_typ);
          current_module_name = (uu___361_3298.current_module_name);
          encoding_quantifier = (uu___361_3298.encoding_quantifier)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3318 = lookup_bvar_binding env a  in
      match uu____3318 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____3330 = lookup_bvar_binding env a2  in
          (match uu____3330 with
           | FStar_Pervasives_Native.None  ->
               let uu____3341 =
                 let uu____3342 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____3343 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____3342 uu____3343
                  in
               failwith uu____3341
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let (mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            fvar_binding)
  =
  fun lid  ->
    fun fname  ->
      fun arity  ->
        fun ftok  ->
          fun fuel_partial_app  ->
            {
              fvar_lid = lid;
              smt_arity = arity;
              smt_id = fname;
              smt_token = ftok;
              smt_fuel_partial_app = fuel_partial_app
            }
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let fname = varops.new_fvar x  in
        let ftok_name = Prims.strcat fname "@tok"  in
        let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
        let fvb =
          mk_fvb x fname arity (FStar_Pervasives_Native.Some ftok)
            FStar_Pervasives_Native.None
           in
        let uu____3416 =
          let uu___362_3417 = env  in
          let uu____3418 = add_fvar_binding fvb env.fvar_bindings  in
          {
            bvar_bindings = (uu___362_3417.bvar_bindings);
            fvar_bindings = uu____3418;
            depth = (uu___362_3417.depth);
            tcenv = (uu___362_3417.tcenv);
            warn = (uu___362_3417.warn);
            cache = (uu___362_3417.cache);
            nolabels = (uu___362_3417.nolabels);
            use_zfuel_name = (uu___362_3417.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___362_3417.encode_non_total_function_typ);
            current_module_name = (uu___362_3417.current_module_name);
            encoding_quantifier = (uu___362_3417.encoding_quantifier)
          }  in
        (fname, ftok_name, uu____3416)
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____3431 = lookup_fvar_binding env a  in
      match uu____3431 with
      | FStar_Pervasives_Native.None  ->
          let uu____3434 =
            let uu____3435 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____3435  in
          failwith uu____3434
      | FStar_Pervasives_Native.Some s -> s
  
let (push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun fname  ->
          fun ftok  ->
            let fvb = mk_fvb x fname arity ftok FStar_Pervasives_Native.None
               in
            let uu___363_3467 = env  in
            let uu____3468 = add_fvar_binding fvb env.fvar_bindings  in
            {
              bvar_bindings = (uu___363_3467.bvar_bindings);
              fvar_bindings = uu____3468;
              depth = (uu___363_3467.depth);
              tcenv = (uu___363_3467.tcenv);
              warn = (uu___363_3467.warn);
              cache = (uu___363_3467.cache);
              nolabels = (uu___363_3467.nolabels);
              use_zfuel_name = (uu___363_3467.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___363_3467.encode_non_total_function_typ);
              current_module_name = (uu___363_3467.current_module_name);
              encoding_quantifier = (uu___363_3467.encoding_quantifier)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____3488 =
            let uu____3495 =
              let uu____3498 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____3498]  in
            (f, uu____3495)  in
          FStar_SMTEncoding_Util.mkApp uu____3488  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___364_3504 = env  in
        let uu____3505 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___364_3504.bvar_bindings);
          fvar_bindings = uu____3505;
          depth = (uu___364_3504.depth);
          tcenv = (uu___364_3504.tcenv);
          warn = (uu___364_3504.warn);
          cache = (uu___364_3504.cache);
          nolabels = (uu___364_3504.nolabels);
          use_zfuel_name = (uu___364_3504.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___364_3504.encode_non_total_function_typ);
          current_module_name = (uu___364_3504.current_module_name);
          encoding_quantifier = (uu___364_3504.encoding_quantifier)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____3520 = lookup_fvar_binding env l  in
      match uu____3520 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____3529 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____3537,fuel::[]) ->
                         let uu____3541 =
                           let uu____3542 =
                             let uu____3543 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____3543
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____3542 "fuel"  in
                         if uu____3541
                         then
                           let uu____3554 =
                             let uu____3555 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____3555
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_16  ->
                                FStar_Pervasives_Native.Some _0_16)
                             uu____3554
                         else FStar_Pervasives_Native.Some t
                     | uu____3559 -> FStar_Pervasives_Native.Some t)
                | uu____3560 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____3577 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____3577 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3581 =
            let uu____3582 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____3582  in
          failwith uu____3581
  
let (lookup_free_var_name :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (Prims.string,Prims.int) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      ((fvb.smt_id), (fvb.smt_arity))
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list,
        Prims.int) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____3635;
            FStar_SMTEncoding_Term.rng = uu____3636;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____3651 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____3679 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.psmap_find_map env.fvar_bindings
        (fun uu____3696  ->
           fun fvb  ->
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  