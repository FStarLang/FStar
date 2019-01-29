open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____9 -> false
  
let add_fuel :
  'Auu____18 . 'Auu____18 -> 'Auu____18 Prims.list -> 'Auu____18 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____35 = FStar_Options.unthrottle_inductives ()  in
      if uu____35 then tl1 else x :: tl1
  
let withenv :
  'Auu____53 'Auu____54 'Auu____55 .
    'Auu____53 ->
      ('Auu____54 * 'Auu____55) -> ('Auu____54 * 'Auu____55 * 'Auu____53)
  = fun c  -> fun uu____75  -> match uu____75 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____91 'Auu____92 'Auu____93 .
    (('Auu____91,'Auu____92) FStar_Util.either * 'Auu____93) Prims.list ->
      (('Auu____91,'Auu____92) FStar_Util.either * 'Auu____93) Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___267_140  ->
         match uu___267_140 with
         | (FStar_Util.Inl uu____150,uu____151) -> false
         | uu____157 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____190 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____190
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____220 =
          let uu____221 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____221  in
        let uu____225 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____225 with
        | (uu____231,t) ->
            let uu____233 =
              let uu____234 = FStar_Syntax_Subst.compress t  in
              uu____234.FStar_Syntax_Syntax.n  in
            (match uu____233 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____260 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____260 with
                  | (binders,uu____267) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____294 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____309 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____309
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____325 =
        let uu____331 = mk_term_projector_name lid a  in
        (uu____331,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____325
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____347 =
        let uu____353 = mk_term_projector_name_by_pos lid i  in
        (uu____353,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____347
  
let mk_data_tester :
  'Auu____365 .
    'Auu____365 ->
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
  snapshot: unit -> (Prims.int * unit) ;
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
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> push1
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> pop1
  
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int * unit)) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> snapshot1
  
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> rollback1
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> fresh1
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> next_id1
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; string_const; next_id = next_id1;
        mk_unique;_} -> mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____1297 =
    let uu____1298 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____1304 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____1298, uu____1304)  in
  let scopes =
    let uu____1327 = let uu____1339 = new_scope ()  in [uu____1339]  in
    FStar_Util.mk_ref uu____1327  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1391 =
        let uu____1395 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1395
          (fun uu____1483  ->
             match uu____1483 with
             | (names1,uu____1497) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1391 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1511 ->
          (FStar_Util.incr ctr;
           (let uu____1548 =
              let uu____1550 =
                let uu____1552 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1552  in
              Prims.strcat "__" uu____1550  in
            Prims.strcat y1 uu____1548))
       in
    let top_scope =
      let uu____1602 =
        let uu____1612 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1612
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1602  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1746 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1833 =
      let uu____1835 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1835  in
    FStar_Util.format2 "%s_%s" pfx uu____1833  in
  let string_const s =
    let uu____1848 =
      let uu____1851 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1851
        (fun uu____1938  ->
           match uu____1938 with
           | (uu____1950,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1848 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1966 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1966  in
        let top_scope =
          let uu____1970 =
            let uu____1980 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1980  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1970  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____2086 =
    let uu____2087 =
      let uu____2099 = new_scope ()  in
      let uu____2109 = FStar_ST.op_Bang scopes  in uu____2099 :: uu____2109
       in
    FStar_ST.op_Colon_Equals scopes uu____2087  in
  let pop1 uu____2261 =
    let uu____2262 =
      let uu____2274 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____2274
       in
    FStar_ST.op_Colon_Equals scopes uu____2262  in
  let snapshot1 uu____2431 = FStar_Common.snapshot push1 scopes ()  in
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
type fvar_binding =
  {
  fvar_lid: FStar_Ident.lident ;
  smt_arity: Prims.int ;
  smt_id: Prims.string ;
  smt_token: FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  smt_fuel_partial_app:
    FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ;
  fvb_thunked: Prims.bool }
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> fvar_lid
  
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_arity
  
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_id
  
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_token
  
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> smt_fuel_partial_app
  
let (__proj__Mkfvar_binding__item__fvb_thunked : fvar_binding -> Prims.bool)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;
        fvb_thunked;_} -> fvb_thunked
  
let binder_of_eithervar :
  'Auu____2678 'Auu____2679 .
    'Auu____2678 ->
      ('Auu____2678 * 'Auu____2679 FStar_Pervasives_Native.option)
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
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_name
  
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_arg_sorts
  
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_decls
  
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name; cache_symbol_arg_sorts; cache_symbol_decls;
        cache_symbol_assumption_names;_} -> cache_symbol_assumption_names
  
type env_t =
  {
  bvar_bindings:
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap
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
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap)
  =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> bvar_bindings
  
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t -> fvar_binding FStar_Util.psmap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> fvar_bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> warn
  
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> cache
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> current_module_name
  
let (__proj__Mkenv_t__item__encoding_quantifier : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; cache; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier;_} -> encoding_quantifier
  
let mk_cache_entry :
  'Auu____3328 .
    'Auu____3328 ->
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
                 (fun uu___268_3371  ->
                    match uu___268_3371 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____3378 -> []))
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
                    fun uu____3438  ->
                      fun acc1  ->
                        match uu____3438 with
                        | (x,_term) ->
                            let uu____3453 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3453 :: acc1) acc) []
       in
    let allvars =
      FStar_Util.psmap_fold e.fvar_bindings
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3476 ->
          let uu____3479 = FStar_Syntax_Print.lid_to_string l  in
          Prims.strcat "...," uu____3479
       in
    FStar_String.concat ", " (last_fvar :: bvars)
  
let (lookup_bvar_binding :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun bv  ->
      let uu____3501 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3501 with
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
  'Auu____3569 .
    (FStar_Syntax_Syntax.bv * 'Auu____3569) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3569) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3569) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3629 =
             let uu____3636 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3636 pimap_opt  in
           FStar_Util.pimap_add uu____3629
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
      (Prims.string * FStar_SMTEncoding_Term.term))
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____3694 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____3694)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      let uu____3720 =
        let uu___269_3721 = env  in
        let uu____3722 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3722;
          fvar_bindings = (uu___269_3721.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___269_3721.tcenv);
          warn = (uu___269_3721.warn);
          cache = (uu___269_3721.cache);
          nolabels = (uu___269_3721.nolabels);
          use_zfuel_name = (uu___269_3721.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___269_3721.encode_non_total_function_typ);
          current_module_name = (uu___269_3721.current_module_name);
          encoding_quantifier = (uu___269_3721.encoding_quantifier)
        }  in
      (ysym, y, uu____3720)
  
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      let uu____3757 =
        let uu___270_3758 = env  in
        let uu____3759 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3759;
          fvar_bindings = (uu___270_3758.fvar_bindings);
          depth = (uu___270_3758.depth);
          tcenv = (uu___270_3758.tcenv);
          warn = (uu___270_3758.warn);
          cache = (uu___270_3758.cache);
          nolabels = (uu___270_3758.nolabels);
          use_zfuel_name = (uu___270_3758.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___270_3758.encode_non_total_function_typ);
          current_module_name = (uu___270_3758.current_module_name);
          encoding_quantifier = (uu___270_3758.encoding_quantifier)
        }  in
      (ysym, y, uu____3757)
  
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        let uu____3800 =
          let uu___271_3801 = env  in
          let uu____3802 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3802;
            fvar_bindings = (uu___271_3801.fvar_bindings);
            depth = (uu___271_3801.depth);
            tcenv = (uu___271_3801.tcenv);
            warn = (uu___271_3801.warn);
            cache = (uu___271_3801.cache);
            nolabels = (uu___271_3801.nolabels);
            use_zfuel_name = (uu___271_3801.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___271_3801.encode_non_total_function_typ);
            current_module_name = (uu___271_3801.current_module_name);
            encoding_quantifier = (uu___271_3801.encoding_quantifier)
          }  in
        (ysym, y, uu____3800)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___272_3828 = env  in
        let uu____3829 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3829;
          fvar_bindings = (uu___272_3828.fvar_bindings);
          depth = (uu___272_3828.depth);
          tcenv = (uu___272_3828.tcenv);
          warn = (uu___272_3828.warn);
          cache = (uu___272_3828.cache);
          nolabels = (uu___272_3828.nolabels);
          use_zfuel_name = (uu___272_3828.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___272_3828.encode_non_total_function_typ);
          current_module_name = (uu___272_3828.current_module_name);
          encoding_quantifier = (uu___272_3828.encoding_quantifier)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3849 = lookup_bvar_binding env a  in
      match uu____3849 with
      | FStar_Pervasives_Native.None  ->
          let uu____3860 = lookup_bvar_binding env a  in
          (match uu____3860 with
           | FStar_Pervasives_Native.None  ->
               let uu____3871 =
                 let uu____3873 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3875 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3873 uu____3875
                  in
               failwith uu____3871
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let (mk_fvb :
  FStar_Ident.lident ->
    Prims.string ->
      Prims.int ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            Prims.bool -> fvar_binding)
  =
  fun lid  ->
    fun fname  ->
      fun arity  ->
        fun ftok  ->
          fun fuel_partial_app  ->
            fun thunked  ->
              {
                fvar_lid = lid;
                smt_arity = arity;
                smt_id = fname;
                smt_token = ftok;
                smt_fuel_partial_app = fuel_partial_app;
                fvb_thunked = thunked
              }
  
let (new_term_constant_and_tok_from_lid_aux :
  env_t ->
    FStar_Ident.lident ->
      Prims.int -> Prims.bool -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun thunked  ->
          let fname = varops.new_fvar x  in
          let ftok_name = Prims.strcat fname "@tok"  in
          let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
          let fvb =
            mk_fvb x fname arity (FStar_Pervasives_Native.Some ftok)
              FStar_Pervasives_Native.None thunked
             in
          let uu____3978 =
            let uu___273_3979 = env  in
            let uu____3980 = add_fvar_binding fvb env.fvar_bindings  in
            {
              bvar_bindings = (uu___273_3979.bvar_bindings);
              fvar_bindings = uu____3980;
              depth = (uu___273_3979.depth);
              tcenv = (uu___273_3979.tcenv);
              warn = (uu___273_3979.warn);
              cache = (uu___273_3979.cache);
              nolabels = (uu___273_3979.nolabels);
              use_zfuel_name = (uu___273_3979.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___273_3979.encode_non_total_function_typ);
              current_module_name = (uu___273_3979.current_module_name);
              encoding_quantifier = (uu___273_3979.encoding_quantifier)
            }  in
          (fname, ftok_name, uu____3978)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  -> new_term_constant_and_tok_from_lid_aux env x arity false
  
let (new_term_constant_and_tok_from_lid_maybe_thunked :
  env_t ->
    FStar_Ident.lident ->
      Prims.int -> Prims.bool -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun th  -> new_term_constant_and_tok_from_lid_aux env x arity th
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____4056 = lookup_fvar_binding env a  in
      match uu____4056 with
      | FStar_Pervasives_Native.None  ->
          let uu____4059 =
            let uu____4061 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4061  in
          failwith uu____4059
      | FStar_Pervasives_Native.Some s -> s
  
let (push_free_var_maybe_thunked :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.string ->
          FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
            Prims.bool -> env_t)
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun fname  ->
          fun ftok  ->
            fun thunked  ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu___274_4107 = env  in
              let uu____4108 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___274_4107.bvar_bindings);
                fvar_bindings = uu____4108;
                depth = (uu___274_4107.depth);
                tcenv = (uu___274_4107.tcenv);
                warn = (uu___274_4107.warn);
                cache = (uu___274_4107.cache);
                nolabels = (uu___274_4107.nolabels);
                use_zfuel_name = (uu___274_4107.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___274_4107.encode_non_total_function_typ);
                current_module_name = (uu___274_4107.current_module_name);
                encoding_quantifier = (uu___274_4107.encoding_quantifier)
              }
  
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
            push_free_var_maybe_thunked env x arity fname ftok false
  
let (push_free_var_thunk :
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
            push_free_var_maybe_thunked env x arity fname ftok
              (arity = (Prims.parse_int "0"))
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____4202 =
            let uu____4210 =
              let uu____4213 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4213]  in
            (f, uu____4210)  in
          FStar_SMTEncoding_Util.mkApp uu____4202  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___275_4223 = env  in
        let uu____4224 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___275_4223.bvar_bindings);
          fvar_bindings = uu____4224;
          depth = (uu___275_4223.depth);
          tcenv = (uu___275_4223.tcenv);
          warn = (uu___275_4223.warn);
          cache = (uu___275_4223.cache);
          nolabels = (uu___275_4223.nolabels);
          use_zfuel_name = (uu___275_4223.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___275_4223.encode_non_total_function_typ);
          current_module_name = (uu___275_4223.current_module_name);
          encoding_quantifier = (uu___275_4223.encoding_quantifier)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4240 = lookup_fvar_binding env l  in
      match uu____4240 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          if fvb.fvb_thunked
          then
            let uu____4249 =
              FStar_SMTEncoding_Util.mkApp
                ((fvb.smt_id), [FStar_SMTEncoding_Term.dummy_value])
               in
            FStar_Pervasives_Native.Some uu____4249
          else
            (match fvb.smt_fuel_partial_app with
             | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                 FStar_Pervasives_Native.Some f
             | uu____4258 ->
                 (match fvb.smt_token with
                  | FStar_Pervasives_Native.Some t ->
                      (match t.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App (uu____4266,fuel::[]) ->
                           let uu____4270 =
                             let uu____4272 =
                               let uu____4274 =
                                 FStar_SMTEncoding_Term.fv_of_term fuel  in
                               FStar_All.pipe_right uu____4274
                                 FStar_Pervasives_Native.fst
                                in
                             FStar_Util.starts_with uu____4272 "fuel"  in
                           if uu____4270
                           then
                             let uu____4291 =
                               let uu____4292 =
                                 FStar_SMTEncoding_Util.mkFreeV
                                   ((fvb.smt_id),
                                     FStar_SMTEncoding_Term.Term_sort)
                                  in
                               FStar_SMTEncoding_Term.mk_ApplyTF uu____4292
                                 fuel
                                in
                             FStar_All.pipe_left
                               (fun _0_1  ->
                                  FStar_Pervasives_Native.Some _0_1)
                               uu____4291
                           else FStar_Pervasives_Native.Some t
                       | uu____4298 -> FStar_Pervasives_Native.Some t)
                  | uu____4299 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4317 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4317 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4321 =
            let uu____4323 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4323  in
          failwith uu____4321
  
let (lookup_free_var_name :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (Prims.string * Prims.int))
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      ((fvb.smt_id), (fvb.smt_arity))
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op * FStar_SMTEncoding_Term.term Prims.list *
        Prims.int))
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____4386;
            FStar_SMTEncoding_Term.rng = uu____4387;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4405 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4438 ->
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
        (fun uu____4459  ->
           fun fvb  ->
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  