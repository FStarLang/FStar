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
    FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option }
let (__proj__Mkfvar_binding__item__fvar_lid :
  fvar_binding -> FStar_Ident.lident) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;_} ->
        fvar_lid
  
let (__proj__Mkfvar_binding__item__smt_arity : fvar_binding -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;_} ->
        smt_arity
  
let (__proj__Mkfvar_binding__item__smt_id : fvar_binding -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;_} ->
        smt_id
  
let (__proj__Mkfvar_binding__item__smt_token :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;_} ->
        smt_token
  
let (__proj__Mkfvar_binding__item__smt_fuel_partial_app :
  fvar_binding -> FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun projectee  ->
    match projectee with
    | { fvar_lid; smt_arity; smt_id; smt_token; smt_fuel_partial_app;_} ->
        smt_fuel_partial_app
  
let binder_of_eithervar :
  'Auu____2641 'Auu____2642 .
    'Auu____2641 ->
      ('Auu____2641 * 'Auu____2642 FStar_Pervasives_Native.option)
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type env_t =
  {
  bvar_bindings:
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap
    ;
  fvar_bindings: (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string ;
  encoding_quantifier: Prims.bool ;
  global_cache: FStar_SMTEncoding_Term.decls_elt FStar_Util.smap ;
  local_cache: FStar_SMTEncoding_Term.decls_elt FStar_Util.smap }
let (__proj__Mkenv_t__item__bvar_bindings :
  env_t ->
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap)
  =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> bvar_bindings
  
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t -> (fvar_binding FStar_Util.psmap * fvar_binding Prims.list)) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> fvar_bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> warn
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} ->
        encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} ->
        current_module_name
  
let (__proj__Mkenv_t__item__encoding_quantifier : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} ->
        encoding_quantifier
  
let (__proj__Mkenv_t__item__global_cache :
  env_t -> FStar_SMTEncoding_Term.decls_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> global_cache
  
let (__proj__Mkenv_t__item__local_cache :
  env_t -> FStar_SMTEncoding_Term.decls_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache; local_cache;_} -> local_cache
  
let (lookup_global_cache :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.decls_elt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tkey_hash  -> FStar_Util.smap_try_find env.global_cache tkey_hash
  
let (add_to_global_cache :
  env_t -> FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun elt  ->
      (let uu____3366 =
         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key FStar_Util.must
          in
       FStar_Util.smap_add env.global_cache uu____3366 elt);
      [elt]
  
let (lookup_local_cache :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.decls_elt FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun tkey_hash  -> FStar_Util.smap_try_find env.local_cache tkey_hash
  
let (add_to_local_cache :
  env_t -> FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun elt  ->
      (let uu____3402 =
         FStar_All.pipe_right elt.FStar_SMTEncoding_Term.key FStar_Util.must
          in
       FStar_Util.smap_add env.local_cache uu____3402 elt);
      [elt]
  
let (use_cache_entry :
  FStar_SMTEncoding_Term.decls_elt -> FStar_SMTEncoding_Term.decls_t) =
  fun elt  ->
    FStar_All.pipe_right
      [FStar_SMTEncoding_Term.RetainAssumptions
         (elt.FStar_SMTEncoding_Term.a_names)]
      FStar_SMTEncoding_Term.mk_decls_trivial
  
let (print_env : env_t -> Prims.string) =
  fun e  ->
    let bvars =
      FStar_Util.psmap_fold e.bvar_bindings
        (fun _k  ->
           fun pi  ->
             fun acc  ->
               FStar_Util.pimap_fold pi
                 (fun _i  ->
                    fun uu____3467  ->
                      fun acc1  ->
                        match uu____3467 with
                        | (x,_term) ->
                            let uu____3482 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3482 :: acc1) acc) []
       in
    let allvars =
      let uu____3489 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____3489
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3522 ->
          let uu____3525 = FStar_Syntax_Print.lid_to_string l  in
          Prims.strcat "...," uu____3525
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
      let uu____3547 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3547 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____3608 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____3608 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3632 .
    (FStar_Syntax_Syntax.bv * 'Auu____3632) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3632) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3632) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3692 =
             let uu____3699 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3699 pimap_opt  in
           FStar_Util.pimap_add uu____3692
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3746  ->
      match uu____3746 with
      | (fvb_map,fvb_list) ->
          let uu____3773 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____3773, (fvb :: fvb_list))
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term))
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____3800 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____3800)
  
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
      let uu____3826 =
        let uu___268_3827 = env  in
        let uu____3828 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3828;
          fvar_bindings = (uu___268_3827.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___268_3827.tcenv);
          warn = (uu___268_3827.warn);
          nolabels = (uu___268_3827.nolabels);
          use_zfuel_name = (uu___268_3827.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___268_3827.encode_non_total_function_typ);
          current_module_name = (uu___268_3827.current_module_name);
          encoding_quantifier = (uu___268_3827.encoding_quantifier);
          global_cache = (uu___268_3827.global_cache);
          local_cache = (uu___268_3827.local_cache)
        }  in
      (ysym, y, uu____3826)
  
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
      let uu____3863 =
        let uu___269_3864 = env  in
        let uu____3865 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3865;
          fvar_bindings = (uu___269_3864.fvar_bindings);
          depth = (uu___269_3864.depth);
          tcenv = (uu___269_3864.tcenv);
          warn = (uu___269_3864.warn);
          nolabels = (uu___269_3864.nolabels);
          use_zfuel_name = (uu___269_3864.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___269_3864.encode_non_total_function_typ);
          current_module_name = (uu___269_3864.current_module_name);
          encoding_quantifier = (uu___269_3864.encoding_quantifier);
          global_cache = (uu___269_3864.global_cache);
          local_cache = (uu___269_3864.local_cache)
        }  in
      (ysym, y, uu____3863)
  
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
        let uu____3906 =
          let uu___270_3907 = env  in
          let uu____3908 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3908;
            fvar_bindings = (uu___270_3907.fvar_bindings);
            depth = (uu___270_3907.depth);
            tcenv = (uu___270_3907.tcenv);
            warn = (uu___270_3907.warn);
            nolabels = (uu___270_3907.nolabels);
            use_zfuel_name = (uu___270_3907.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___270_3907.encode_non_total_function_typ);
            current_module_name = (uu___270_3907.current_module_name);
            encoding_quantifier = (uu___270_3907.encoding_quantifier);
            global_cache = (uu___270_3907.global_cache);
            local_cache = (uu___270_3907.local_cache)
          }  in
        (ysym, y, uu____3906)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___271_3934 = env  in
        let uu____3935 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3935;
          fvar_bindings = (uu___271_3934.fvar_bindings);
          depth = (uu___271_3934.depth);
          tcenv = (uu___271_3934.tcenv);
          warn = (uu___271_3934.warn);
          nolabels = (uu___271_3934.nolabels);
          use_zfuel_name = (uu___271_3934.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___271_3934.encode_non_total_function_typ);
          current_module_name = (uu___271_3934.current_module_name);
          encoding_quantifier = (uu___271_3934.encoding_quantifier);
          global_cache = (uu___271_3934.global_cache);
          local_cache = (uu___271_3934.local_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3955 = lookup_bvar_binding env a  in
      match uu____3955 with
      | FStar_Pervasives_Native.None  ->
          let uu____3966 = lookup_bvar_binding env a  in
          (match uu____3966 with
           | FStar_Pervasives_Native.None  ->
               let uu____3977 =
                 let uu____3979 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3981 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3979 uu____3981
                  in
               failwith uu____3977
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
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
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
        let uu____4070 =
          let uu___272_4071 = env  in
          let uu____4072 = add_fvar_binding fvb env.fvar_bindings  in
          {
            bvar_bindings = (uu___272_4071.bvar_bindings);
            fvar_bindings = uu____4072;
            depth = (uu___272_4071.depth);
            tcenv = (uu___272_4071.tcenv);
            warn = (uu___272_4071.warn);
            nolabels = (uu___272_4071.nolabels);
            use_zfuel_name = (uu___272_4071.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___272_4071.encode_non_total_function_typ);
            current_module_name = (uu___272_4071.current_module_name);
            encoding_quantifier = (uu___272_4071.encoding_quantifier);
            global_cache = (uu___272_4071.global_cache);
            local_cache = (uu___272_4071.local_cache)
          }  in
        (fname, ftok_name, uu____4070)
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____4094 = lookup_fvar_binding env a  in
      match uu____4094 with
      | FStar_Pervasives_Native.None  ->
          let uu____4097 =
            let uu____4099 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4099  in
          failwith uu____4097
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
            let uu___273_4138 = env  in
            let uu____4139 = add_fvar_binding fvb env.fvar_bindings  in
            {
              bvar_bindings = (uu___273_4138.bvar_bindings);
              fvar_bindings = uu____4139;
              depth = (uu___273_4138.depth);
              tcenv = (uu___273_4138.tcenv);
              warn = (uu___273_4138.warn);
              nolabels = (uu___273_4138.nolabels);
              use_zfuel_name = (uu___273_4138.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___273_4138.encode_non_total_function_typ);
              current_module_name = (uu___273_4138.current_module_name);
              encoding_quantifier = (uu___273_4138.encoding_quantifier);
              global_cache = (uu___273_4138.global_cache);
              local_cache = (uu___273_4138.local_cache)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____4168 =
            let uu____4176 =
              let uu____4179 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4179]  in
            (f, uu____4176)  in
          FStar_SMTEncoding_Util.mkApp uu____4168  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___274_4188 = env  in
        let uu____4189 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___274_4188.bvar_bindings);
          fvar_bindings = uu____4189;
          depth = (uu___274_4188.depth);
          tcenv = (uu___274_4188.tcenv);
          warn = (uu___274_4188.warn);
          nolabels = (uu___274_4188.nolabels);
          use_zfuel_name = (uu___274_4188.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___274_4188.encode_non_total_function_typ);
          current_module_name = (uu___274_4188.current_module_name);
          encoding_quantifier = (uu___274_4188.encoding_quantifier);
          global_cache = (uu___274_4188.global_cache);
          local_cache = (uu___274_4188.local_cache)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4211 = lookup_fvar_binding env l  in
      match uu____4211 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____4220 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____4228,fuel::[]) ->
                         let uu____4232 =
                           let uu____4234 =
                             let uu____4236 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____4236
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____4234 "fuel"  in
                         if uu____4232
                         then
                           let uu____4253 =
                             let uu____4254 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____4254
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                             uu____4253
                         else FStar_Pervasives_Native.Some t
                     | uu____4260 -> FStar_Pervasives_Native.Some t)
                | uu____4261 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4279 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4279 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4283 =
            let uu____4285 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4285  in
          failwith uu____4283
  
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
            FStar_SMTEncoding_Term.freevars = uu____4348;
            FStar_SMTEncoding_Term.rng = uu____4349;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4367 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4400 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      let uu____4419 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_find_map uu____4419
        (fun uu____4438  ->
           fun fvb  ->
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    FStar_Util.smap_clear env.local_cache;
    (let uu___275_4454 = env  in
     let uu____4455 =
       let uu____4464 =
         FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
          in
       (uu____4464, [])  in
     {
       bvar_bindings = (uu___275_4454.bvar_bindings);
       fvar_bindings = uu____4455;
       depth = (uu___275_4454.depth);
       tcenv = (uu___275_4454.tcenv);
       warn = (uu___275_4454.warn);
       nolabels = (uu___275_4454.nolabels);
       use_zfuel_name = (uu___275_4454.use_zfuel_name);
       encode_non_total_function_typ =
         (uu___275_4454.encode_non_total_function_typ);
       current_module_name = (uu___275_4454.current_module_name);
       encoding_quantifier = (uu___275_4454.encoding_quantifier);
       global_cache = (uu___275_4454.global_cache);
       local_cache = (uu___275_4454.local_cache)
     })
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___276_4518 = env  in
      let uu____4519 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___276_4518.bvar_bindings);
        fvar_bindings = uu____4519;
        depth = (uu___276_4518.depth);
        tcenv = (uu___276_4518.tcenv);
        warn = (uu___276_4518.warn);
        nolabels = (uu___276_4518.nolabels);
        use_zfuel_name = (uu___276_4518.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___276_4518.encode_non_total_function_typ);
        current_module_name = (uu___276_4518.current_module_name);
        encoding_quantifier = (uu___276_4518.encoding_quantifier);
        global_cache = (uu___276_4518.global_cache);
        local_cache = (uu___276_4518.local_cache)
      }
  