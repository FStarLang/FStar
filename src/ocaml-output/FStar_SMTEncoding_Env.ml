open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____36 -> false
  
let add_fuel :
  'Auu____45 . 'Auu____45 -> 'Auu____45 Prims.list -> 'Auu____45 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____62 = FStar_Options.unthrottle_inductives ()  in
      if uu____62 then tl1 else x :: tl1
  
let withenv :
  'Auu____80 'Auu____81 'Auu____82 .
    'Auu____80 ->
      ('Auu____81 * 'Auu____82) -> ('Auu____81 * 'Auu____82 * 'Auu____80)
  = fun c  -> fun uu____102  -> match uu____102 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____118 'Auu____119 'Auu____120 .
    (('Auu____118,'Auu____119) FStar_Util.either * 'Auu____120) Prims.list ->
      (('Auu____118,'Auu____119) FStar_Util.either * 'Auu____120) Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___0_167  ->
         match uu___0_167 with
         | (FStar_Util.Inl uu____177,uu____178) -> false
         | uu____184 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____217 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____217
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____247 =
          let uu____248 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____248  in
        let uu____252 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____252 with
        | (uu____258,t) ->
            let uu____260 =
              let uu____261 = FStar_Syntax_Subst.compress t  in
              uu____261.FStar_Syntax_Syntax.n  in
            (match uu____260 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____287 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____287 with
                  | (binders,uu____294) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____321 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____336 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____336
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____352 =
        let uu____353 =
          let uu____359 = mk_term_projector_name lid a  in
          (uu____359,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____353  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____352
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____375 =
        let uu____376 =
          let uu____382 = mk_term_projector_name_by_pos lid i  in
          (uu____382,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____376  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____375
  
let mk_data_tester :
  'Auu____394 .
    'Auu____394 ->
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
  fresh: Prims.string -> Prims.string -> Prims.string ;
  reset_fresh: unit -> unit ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }
let (__proj__Mkvarops_t__item__push : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> push1
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> pop1
  
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int * unit)) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> snapshot1
  
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> rollback1
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> fresh1
  
let (__proj__Mkvarops_t__item__reset_fresh : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> reset_fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> next_id1
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = push1; pop = pop1; snapshot = snapshot1; rollback = rollback1;
        new_var; new_fvar; fresh = fresh1; reset_fresh; string_const;
        next_id = next_id1; mk_unique;_} -> mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____1512 =
    let uu____1513 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____1519 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____1513, uu____1519)  in
  let scopes =
    let uu____1542 = let uu____1554 = new_scope ()  in [uu____1554]  in
    FStar_Util.mk_ref uu____1542  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1606 =
        let uu____1610 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1610
          (fun uu____1676  ->
             match uu____1676 with
             | (names1,uu____1690) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1606 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1704 ->
          (FStar_Util.incr ctr;
           (let uu____1708 =
              let uu____1710 =
                let uu____1712 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1712  in
              Prims.op_Hat "__" uu____1710  in
            Prims.op_Hat y1 uu____1708))
       in
    let top_scope =
      let uu____1740 =
        let uu____1750 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1750
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1740  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.op_Hat pp.FStar_Ident.idText
         (Prims.op_Hat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1862 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 mname pfx =
    let uu____1901 =
      let uu____1903 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1903  in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____1901  in
  let reset_fresh uu____1913 = FStar_ST.op_Colon_Equals ctr initial_ctr  in
  let string_const s =
    let uu____1943 =
      let uu____1946 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1946
        (fun uu____2011  ->
           match uu____2011 with
           | (uu____2023,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1943 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____2039 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2039  in
        let top_scope =
          let uu____2043 =
            let uu____2053 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____2053  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2043  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____2137 =
    let uu____2138 =
      let uu____2150 = new_scope ()  in
      let uu____2160 = FStar_ST.op_Bang scopes  in uu____2150 :: uu____2160
       in
    FStar_ST.op_Colon_Equals scopes uu____2138  in
  let pop1 uu____2268 =
    let uu____2269 =
      let uu____2281 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____2281
       in
    FStar_ST.op_Colon_Equals scopes uu____2269  in
  let snapshot1 uu____2394 = FStar_Common.snapshot push1 scopes ()  in
  let rollback1 depth = FStar_Common.rollback pop1 scopes depth  in
  {
    push = push1;
    pop = pop1;
    snapshot = snapshot1;
    rollback = rollback1;
    new_var;
    new_fvar;
    fresh = fresh1;
    reset_fresh;
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
  
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb  ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      let uu____2597 =
        let uu____2599 = FStar_Ident.string_of_lid fvb.fvar_lid  in
        FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2599  in
      failwith uu____2597
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> (Prims.parse_int "0"))
      then
        (let uu____2607 =
           let uu____2609 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____2609
            in
         failwith uu____2607)
      else ()
  
let binder_of_eithervar :
  'Auu____2621 'Auu____2622 .
    'Auu____2621 ->
      ('Auu____2621 * 'Auu____2622 FStar_Pervasives_Native.option)
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
  global_cache: FStar_SMTEncoding_Term.decls_elt FStar_Util.smap }
let (__proj__Mkenv_t__item__bvar_bindings :
  env_t ->
    (FStar_Syntax_Syntax.bv * FStar_SMTEncoding_Term.term) FStar_Util.pimap
      FStar_Util.psmap)
  =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> bvar_bindings
  
let (__proj__Mkenv_t__item__fvar_bindings :
  env_t -> (fvar_binding FStar_Util.psmap * fvar_binding Prims.list)) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> fvar_bindings
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> depth
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> tcenv
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> warn
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> nolabels
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> use_zfuel_name
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> encode_non_total_function_typ
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> current_module_name
  
let (__proj__Mkenv_t__item__encoding_quantifier : env_t -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> encoding_quantifier
  
let (__proj__Mkenv_t__item__global_cache :
  env_t -> FStar_SMTEncoding_Term.decls_elt FStar_Util.smap) =
  fun projectee  ->
    match projectee with
    | { bvar_bindings; fvar_bindings; depth; tcenv; warn; nolabels;
        use_zfuel_name; encode_non_total_function_typ; current_module_name;
        encoding_quantifier; global_cache;_} -> global_cache
  
let (print_env : env_t -> Prims.string) =
  fun e  ->
    let bvars =
      FStar_Util.psmap_fold e.bvar_bindings
        (fun _k  ->
           fun pi  ->
             fun acc  ->
               FStar_Util.pimap_fold pi
                 (fun _i  ->
                    fun uu____3278  ->
                      fun acc1  ->
                        match uu____3278 with
                        | (x,_term) ->
                            let uu____3293 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3293 :: acc1) acc) []
       in
    let allvars =
      let uu____3300 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____3300
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3333 ->
          let uu____3336 = FStar_Syntax_Print.lid_to_string l  in
          Prims.op_Hat "...," uu____3336
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
      let uu____3358 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3358 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____3419 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____3419 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3443 .
    (FStar_Syntax_Syntax.bv * 'Auu____3443) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3443) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3443) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3503 =
             let uu____3510 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3510 pimap_opt  in
           FStar_Util.pimap_add uu____3503
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3557  ->
      match uu____3557 with
      | (fvb_map,fvb_list) ->
          let uu____3584 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____3584, (fvb :: fvb_list))
  
let (fresh_fvar :
  Prims.string ->
    Prims.string ->
      FStar_SMTEncoding_Term.sort ->
        (Prims.string * FStar_SMTEncoding_Term.term))
  =
  fun mname  ->
    fun x  ->
      fun s  ->
        let xsym = varops.fresh mname x  in
        let uu____3618 =
          let uu____3619 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3619  in
        (xsym, uu____3618)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____3644 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3644  in
      let uu____3646 =
        let uu___225_3647 = env  in
        let uu____3648 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3648;
          fvar_bindings = (uu___225_3647.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___225_3647.tcenv);
          warn = (uu___225_3647.warn);
          nolabels = (uu___225_3647.nolabels);
          use_zfuel_name = (uu___225_3647.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___225_3647.encode_non_total_function_typ);
          current_module_name = (uu___225_3647.current_module_name);
          encoding_quantifier = (uu___225_3647.encoding_quantifier);
          global_cache = (uu___225_3647.global_cache)
        }  in
      (ysym, y, uu____3646)
  
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
      let uu____3683 =
        let uu___231_3684 = env  in
        let uu____3685 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3685;
          fvar_bindings = (uu___231_3684.fvar_bindings);
          depth = (uu___231_3684.depth);
          tcenv = (uu___231_3684.tcenv);
          warn = (uu___231_3684.warn);
          nolabels = (uu___231_3684.nolabels);
          use_zfuel_name = (uu___231_3684.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___231_3684.encode_non_total_function_typ);
          current_module_name = (uu___231_3684.current_module_name);
          encoding_quantifier = (uu___231_3684.encoding_quantifier);
          global_cache = (uu___231_3684.global_cache)
        }  in
      (ysym, y, uu____3683)
  
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
        let uu____3726 =
          let uu___238_3727 = env  in
          let uu____3728 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3728;
            fvar_bindings = (uu___238_3727.fvar_bindings);
            depth = (uu___238_3727.depth);
            tcenv = (uu___238_3727.tcenv);
            warn = (uu___238_3727.warn);
            nolabels = (uu___238_3727.nolabels);
            use_zfuel_name = (uu___238_3727.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___238_3727.encode_non_total_function_typ);
            current_module_name = (uu___238_3727.current_module_name);
            encoding_quantifier = (uu___238_3727.encoding_quantifier);
            global_cache = (uu___238_3727.global_cache)
          }  in
        (ysym, y, uu____3726)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___243_3754 = env  in
        let uu____3755 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3755;
          fvar_bindings = (uu___243_3754.fvar_bindings);
          depth = (uu___243_3754.depth);
          tcenv = (uu___243_3754.tcenv);
          warn = (uu___243_3754.warn);
          nolabels = (uu___243_3754.nolabels);
          use_zfuel_name = (uu___243_3754.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___243_3754.encode_non_total_function_typ);
          current_module_name = (uu___243_3754.current_module_name);
          encoding_quantifier = (uu___243_3754.encoding_quantifier);
          global_cache = (uu___243_3754.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3775 = lookup_bvar_binding env a  in
      match uu____3775 with
      | FStar_Pervasives_Native.None  ->
          let uu____3786 = lookup_bvar_binding env a  in
          (match uu____3786 with
           | FStar_Pervasives_Native.None  ->
               let uu____3797 =
                 let uu____3799 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3801 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3799 uu____3801
                  in
               failwith uu____3797
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
              let fvb =
                {
                  fvar_lid = lid;
                  smt_arity = arity;
                  smt_id = fname;
                  smt_token = ftok;
                  smt_fuel_partial_app = fuel_partial_app;
                  fvb_thunked = thunked
                }  in
              check_valid_fvb fvb; fvb
  
let (new_term_constant_and_tok_from_lid_aux :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.bool ->
          (Prims.string * Prims.string FStar_Pervasives_Native.option *
            env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun thunked  ->
          let fname = varops.new_fvar x  in
          let uu____3900 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____3900 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____3964 =
                let uu___277_3965 = env  in
                let uu____3966 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___277_3965.bvar_bindings);
                  fvar_bindings = uu____3966;
                  depth = (uu___277_3965.depth);
                  tcenv = (uu___277_3965.tcenv);
                  warn = (uu___277_3965.warn);
                  nolabels = (uu___277_3965.nolabels);
                  use_zfuel_name = (uu___277_3965.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___277_3965.encode_non_total_function_typ);
                  current_module_name = (uu___277_3965.current_module_name);
                  encoding_quantifier = (uu___277_3965.encoding_quantifier);
                  global_cache = (uu___277_3965.global_cache)
                }  in
              (fname, ftok_name, uu____3964)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____4005 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____4005 with
        | (fname,ftok_name_opt,env1) ->
            let uu____4036 = FStar_Option.get ftok_name_opt  in
            (fname, uu____4036, env1)
  
let (new_term_constant_and_tok_from_lid_maybe_thunked :
  env_t ->
    FStar_Ident.lident ->
      Prims.int ->
        Prims.bool ->
          (Prims.string * Prims.string FStar_Pervasives_Native.option *
            env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        fun th  -> new_term_constant_and_tok_from_lid_aux env x arity th
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____4087 = lookup_fvar_binding env a  in
      match uu____4087 with
      | FStar_Pervasives_Native.None  ->
          let uu____4090 =
            let uu____4092 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4092  in
          failwith uu____4090
      | FStar_Pervasives_Native.Some s -> (check_valid_fvb s; s)
  
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
              let uu___303_4139 = env  in
              let uu____4140 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___303_4139.bvar_bindings);
                fvar_bindings = uu____4140;
                depth = (uu___303_4139.depth);
                tcenv = (uu___303_4139.tcenv);
                warn = (uu___303_4139.warn);
                nolabels = (uu___303_4139.nolabels);
                use_zfuel_name = (uu___303_4139.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___303_4139.encode_non_total_function_typ);
                current_module_name = (uu___303_4139.current_module_name);
                encoding_quantifier = (uu___303_4139.encoding_quantifier);
                global_cache = (uu___303_4139.global_cache)
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
          let uu____4240 =
            let uu____4248 =
              let uu____4251 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4251]  in
            (f, uu____4248)  in
          FStar_SMTEncoding_Util.mkApp uu____4240  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___321_4261 = env  in
        let uu____4262 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___321_4261.bvar_bindings);
          fvar_bindings = uu____4262;
          depth = (uu___321_4261.depth);
          tcenv = (uu___321_4261.tcenv);
          warn = (uu___321_4261.warn);
          nolabels = (uu___321_4261.nolabels);
          use_zfuel_name = (uu___321_4261.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___321_4261.encode_non_total_function_typ);
          current_module_name = (uu___321_4261.current_module_name);
          encoding_quantifier = (uu___321_4261.encoding_quantifier);
          global_cache = (uu___321_4261.global_cache)
        }
  
let (force_thunk : fvar_binding -> FStar_SMTEncoding_Term.term) =
  fun fvb  ->
    if
      (Prims.op_Negation fvb.fvb_thunked) ||
        (fvb.smt_arity <> (Prims.parse_int "0"))
    then failwith "Forcing a non-thunk in the SMT encoding"
    else ();
    FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV
      ((fvb.smt_id), FStar_SMTEncoding_Term.Term_sort, true)
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4300 = lookup_fvar_binding env l  in
      match uu____4300 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          if fvb.fvb_thunked
          then
            let uu____4309 = force_thunk fvb  in
            FStar_Pervasives_Native.Some uu____4309
          else
            (match fvb.smt_fuel_partial_app with
             | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                 FStar_Pervasives_Native.Some f
             | uu____4315 ->
                 (match fvb.smt_token with
                  | FStar_Pervasives_Native.Some t ->
                      (match t.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App (uu____4323,fuel::[]) ->
                           let uu____4327 =
                             let uu____4329 =
                               let uu____4331 =
                                 FStar_SMTEncoding_Term.fv_of_term fuel  in
                               FStar_All.pipe_right uu____4331
                                 FStar_SMTEncoding_Term.fv_name
                                in
                             FStar_Util.starts_with uu____4329 "fuel"  in
                           if uu____4327
                           then
                             let uu____4337 =
                               let uu____4338 =
                                 let uu____4339 =
                                   FStar_SMTEncoding_Term.mk_fv
                                     ((fvb.smt_id),
                                       FStar_SMTEncoding_Term.Term_sort)
                                    in
                                 FStar_All.pipe_left
                                   FStar_SMTEncoding_Util.mkFreeV uu____4339
                                  in
                               FStar_SMTEncoding_Term.mk_ApplyTF uu____4338
                                 fuel
                                in
                             FStar_All.pipe_left
                               (fun _4343  ->
                                  FStar_Pervasives_Native.Some _4343)
                               uu____4337
                           else FStar_Pervasives_Native.Some t
                       | uu____4346 -> FStar_Pervasives_Native.Some t)
                  | uu____4347 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4365 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4365 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4369 =
            let uu____4371 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4371  in
          failwith uu____4369
  
let (lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> fvar_binding)
  = fun env  -> fun a  -> lookup_lid env a.FStar_Syntax_Syntax.v 
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      ((FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term)
        FStar_Util.either * FStar_SMTEncoding_Term.term Prims.list *
        Prims.int))
  =
  fun env  ->
    fun a  ->
      let fvb = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match fvb.smt_fuel_partial_app with
      | FStar_Pervasives_Native.Some
          { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
            FStar_SMTEncoding_Term.freevars = uu____4433;
            FStar_SMTEncoding_Term.rng = uu____4434;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4459 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____4475 =
                 let uu____4480 = force_thunk fvb  in
                 FStar_Util.Inr uu____4480  in
               (uu____4475, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4521 ->
                    ((FStar_Util.Inl
                        (FStar_SMTEncoding_Term.Var (fvb.smt_id))), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      let uu____4544 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_find_map uu____4544
        (fun uu____4564  ->
           fun fvb  ->
             check_valid_fvb fvb;
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___381_4580 = env  in
    let uu____4581 =
      let uu____4590 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____4590, [])  in
    {
      bvar_bindings = (uu___381_4580.bvar_bindings);
      fvar_bindings = uu____4581;
      depth = (uu___381_4580.depth);
      tcenv = (uu___381_4580.tcenv);
      warn = (uu___381_4580.warn);
      nolabels = (uu___381_4580.nolabels);
      use_zfuel_name = (uu___381_4580.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___381_4580.encode_non_total_function_typ);
      current_module_name = (uu___381_4580.current_module_name);
      encoding_quantifier = (uu___381_4580.encoding_quantifier);
      global_cache = (uu___381_4580.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___386_4644 = env  in
      let uu____4645 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___386_4644.bvar_bindings);
        fvar_bindings = uu____4645;
        depth = (uu___386_4644.depth);
        tcenv = (uu___386_4644.tcenv);
        warn = (uu___386_4644.warn);
        nolabels = (uu___386_4644.nolabels);
        use_zfuel_name = (uu___386_4644.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___386_4644.encode_non_total_function_typ);
        current_module_name = (uu___386_4644.current_module_name);
        encoding_quantifier = (uu___386_4644.encoding_quantifier);
        global_cache = (uu___386_4644.global_cache)
      }
  