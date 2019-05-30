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
  
let (fvb_to_string : fvar_binding -> Prims.string) =
  fun fvb  ->
    let term_opt_to_string uu___1_2605 =
      match uu___1_2605 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some s ->
          FStar_SMTEncoding_Term.print_smt_term s
       in
    let uu____2611 = FStar_Ident.string_of_lid fvb.fvar_lid  in
    let uu____2613 = term_opt_to_string fvb.smt_token  in
    let uu____2615 = term_opt_to_string fvb.smt_fuel_partial_app  in
    let uu____2617 = FStar_Util.string_of_bool fvb.fvb_thunked  in
    FStar_Util.format5
      "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }"
      uu____2611 fvb.smt_id uu____2613 uu____2615 uu____2617
  
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb  ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      (let uu____2628 =
         let uu____2630 = FStar_Ident.string_of_lid fvb.fvar_lid  in
         FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2630
          in
       failwith uu____2628)
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> (Prims.parse_int "0"))
      then
        (let uu____2638 =
           let uu____2640 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____2640
            in
         failwith uu____2638)
      else ();
    (match fvb.smt_token with
     | FStar_Pervasives_Native.Some
         {
           FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
             uu____2645;
           FStar_SMTEncoding_Term.freevars = uu____2646;
           FStar_SMTEncoding_Term.rng = uu____2647;_}
         ->
         let uu____2668 =
           let uu____2670 = fvb_to_string fvb  in
           FStar_Util.format1 "bad fvb\n%s" uu____2670  in
         failwith uu____2668
     | uu____2673 -> ())
  
let binder_of_eithervar :
  'Auu____2683 'Auu____2684 .
    'Auu____2683 ->
      ('Auu____2683 * 'Auu____2684 FStar_Pervasives_Native.option)
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
                    fun uu____3340  ->
                      fun acc1  ->
                        match uu____3340 with
                        | (x,_term) ->
                            let uu____3355 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3355 :: acc1) acc) []
       in
    let allvars =
      let uu____3362 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____3362
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3395 ->
          let uu____3398 = FStar_Syntax_Print.lid_to_string l  in
          Prims.op_Hat "...," uu____3398
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
      let uu____3420 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3420 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____3481 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____3481 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3505 .
    (FStar_Syntax_Syntax.bv * 'Auu____3505) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3505) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3505) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3565 =
             let uu____3572 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3572 pimap_opt  in
           FStar_Util.pimap_add uu____3565
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3619  ->
      match uu____3619 with
      | (fvb_map,fvb_list) ->
          let uu____3646 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____3646, (fvb :: fvb_list))
  
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
        let uu____3680 =
          let uu____3681 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3681  in
        (xsym, uu____3680)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____3706 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3706  in
      let uu____3708 =
        let uu___240_3709 = env  in
        let uu____3710 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3710;
          fvar_bindings = (uu___240_3709.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___240_3709.tcenv);
          warn = (uu___240_3709.warn);
          nolabels = (uu___240_3709.nolabels);
          use_zfuel_name = (uu___240_3709.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___240_3709.encode_non_total_function_typ);
          current_module_name = (uu___240_3709.current_module_name);
          encoding_quantifier = (uu___240_3709.encoding_quantifier);
          global_cache = (uu___240_3709.global_cache)
        }  in
      (ysym, y, uu____3708)
  
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
      let uu____3745 =
        let uu___246_3746 = env  in
        let uu____3747 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3747;
          fvar_bindings = (uu___246_3746.fvar_bindings);
          depth = (uu___246_3746.depth);
          tcenv = (uu___246_3746.tcenv);
          warn = (uu___246_3746.warn);
          nolabels = (uu___246_3746.nolabels);
          use_zfuel_name = (uu___246_3746.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___246_3746.encode_non_total_function_typ);
          current_module_name = (uu___246_3746.current_module_name);
          encoding_quantifier = (uu___246_3746.encoding_quantifier);
          global_cache = (uu___246_3746.global_cache)
        }  in
      (ysym, y, uu____3745)
  
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
        let uu____3788 =
          let uu___253_3789 = env  in
          let uu____3790 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3790;
            fvar_bindings = (uu___253_3789.fvar_bindings);
            depth = (uu___253_3789.depth);
            tcenv = (uu___253_3789.tcenv);
            warn = (uu___253_3789.warn);
            nolabels = (uu___253_3789.nolabels);
            use_zfuel_name = (uu___253_3789.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___253_3789.encode_non_total_function_typ);
            current_module_name = (uu___253_3789.current_module_name);
            encoding_quantifier = (uu___253_3789.encoding_quantifier);
            global_cache = (uu___253_3789.global_cache)
          }  in
        (ysym, y, uu____3788)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___258_3816 = env  in
        let uu____3817 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3817;
          fvar_bindings = (uu___258_3816.fvar_bindings);
          depth = (uu___258_3816.depth);
          tcenv = (uu___258_3816.tcenv);
          warn = (uu___258_3816.warn);
          nolabels = (uu___258_3816.nolabels);
          use_zfuel_name = (uu___258_3816.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___258_3816.encode_non_total_function_typ);
          current_module_name = (uu___258_3816.current_module_name);
          encoding_quantifier = (uu___258_3816.encoding_quantifier);
          global_cache = (uu___258_3816.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3837 = lookup_bvar_binding env a  in
      match uu____3837 with
      | FStar_Pervasives_Native.None  ->
          let uu____3848 = lookup_bvar_binding env a  in
          (match uu____3848 with
           | FStar_Pervasives_Native.None  ->
               let uu____3859 =
                 let uu____3861 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3863 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3861 uu____3863
                  in
               failwith uu____3859
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
          let uu____3962 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____3962 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____4026 =
                let uu___292_4027 = env  in
                let uu____4028 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___292_4027.bvar_bindings);
                  fvar_bindings = uu____4028;
                  depth = (uu___292_4027.depth);
                  tcenv = (uu___292_4027.tcenv);
                  warn = (uu___292_4027.warn);
                  nolabels = (uu___292_4027.nolabels);
                  use_zfuel_name = (uu___292_4027.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___292_4027.encode_non_total_function_typ);
                  current_module_name = (uu___292_4027.current_module_name);
                  encoding_quantifier = (uu___292_4027.encoding_quantifier);
                  global_cache = (uu___292_4027.global_cache)
                }  in
              (fname, ftok_name, uu____4026)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____4067 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____4067 with
        | (fname,ftok_name_opt,env1) ->
            let uu____4098 = FStar_Option.get ftok_name_opt  in
            (fname, uu____4098, env1)
  
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
      let uu____4149 = lookup_fvar_binding env a  in
      match uu____4149 with
      | FStar_Pervasives_Native.None  ->
          let uu____4152 =
            let uu____4154 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4154  in
          failwith uu____4152
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
              let uu___318_4201 = env  in
              let uu____4202 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___318_4201.bvar_bindings);
                fvar_bindings = uu____4202;
                depth = (uu___318_4201.depth);
                tcenv = (uu___318_4201.tcenv);
                warn = (uu___318_4201.warn);
                nolabels = (uu___318_4201.nolabels);
                use_zfuel_name = (uu___318_4201.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___318_4201.encode_non_total_function_typ);
                current_module_name = (uu___318_4201.current_module_name);
                encoding_quantifier = (uu___318_4201.encoding_quantifier);
                global_cache = (uu___318_4201.global_cache)
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
          let uu____4302 =
            let uu____4310 =
              let uu____4313 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4313]  in
            (f, uu____4310)  in
          FStar_SMTEncoding_Util.mkApp uu____4302  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___336_4323 = env  in
        let uu____4324 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___336_4323.bvar_bindings);
          fvar_bindings = uu____4324;
          depth = (uu___336_4323.depth);
          tcenv = (uu___336_4323.tcenv);
          warn = (uu___336_4323.warn);
          nolabels = (uu___336_4323.nolabels);
          use_zfuel_name = (uu___336_4323.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___336_4323.encode_non_total_function_typ);
          current_module_name = (uu___336_4323.current_module_name);
          encoding_quantifier = (uu___336_4323.encoding_quantifier);
          global_cache = (uu___336_4323.global_cache)
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
      let uu____4362 = lookup_fvar_binding env l  in
      match uu____4362 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          ((let uu____4369 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
                (FStar_Options.Other "PartialApp")
               in
            if uu____4369
            then
              let uu____4374 = FStar_Ident.string_of_lid l  in
              let uu____4376 = fvb_to_string fvb  in
              FStar_Util.print2 "Looked up %s found\n%s\n" uu____4374
                uu____4376
            else ());
           if fvb.fvb_thunked
           then
             (let uu____4384 = force_thunk fvb  in
              FStar_Pervasives_Native.Some uu____4384)
           else
             (match fvb.smt_fuel_partial_app with
              | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                  FStar_Pervasives_Native.Some f
              | uu____4390 ->
                  (match fvb.smt_token with
                   | FStar_Pervasives_Native.Some t ->
                       (match t.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App (uu____4398,fuel::[]) ->
                            let uu____4402 =
                              let uu____4404 =
                                let uu____4406 =
                                  FStar_SMTEncoding_Term.fv_of_term fuel  in
                                FStar_All.pipe_right uu____4406
                                  FStar_SMTEncoding_Term.fv_name
                                 in
                              FStar_Util.starts_with uu____4404 "fuel"  in
                            if uu____4402
                            then
                              let uu____4412 =
                                let uu____4413 =
                                  let uu____4414 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ((fvb.smt_id),
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Util.mkFreeV uu____4414
                                   in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu____4413
                                  fuel
                                 in
                              FStar_All.pipe_left
                                (fun _4418  ->
                                   FStar_Pervasives_Native.Some _4418)
                                uu____4412
                            else FStar_Pervasives_Native.Some t
                        | uu____4421 -> FStar_Pervasives_Native.Some t)
                   | uu____4422 -> FStar_Pervasives_Native.None)))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4440 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4440 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4444 =
            let uu____4446 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4446  in
          failwith uu____4444
  
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
            FStar_SMTEncoding_Term.freevars = uu____4508;
            FStar_SMTEncoding_Term.rng = uu____4509;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4534 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____4550 =
                 let uu____4555 = force_thunk fvb  in
                 FStar_Util.Inr uu____4555  in
               (uu____4550, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4596 ->
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
      let uu____4619 =
        let uu____4622 =
          FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
           in
        FStar_Util.psmap_find_map uu____4622
          (fun uu____4642  ->
             fun fvb  ->
               check_valid_fvb fvb;
               if fvb.smt_id = nm
               then fvb.smt_token
               else FStar_Pervasives_Native.None)
         in
      match uu____4619 with
      | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
      | FStar_Pervasives_Native.None  ->
          FStar_Util.psmap_find_map env.bvar_bindings
            (fun uu____4663  ->
               fun pi  ->
                 FStar_Util.pimap_fold pi
                   (fun uu____4683  ->
                      fun y  ->
                        fun res  ->
                          match (res, y) with
                          | (FStar_Pervasives_Native.Some
                             uu____4701,uu____4702) -> res
                          | (FStar_Pervasives_Native.None
                             ,(uu____4713,{
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Var
                                               sym,[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____4715;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____4716;_}))
                              when sym = nm ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.snd y)
                          | uu____4739 -> FStar_Pervasives_Native.None)
                   FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___423_4756 = env  in
    let uu____4757 =
      let uu____4766 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____4766, [])  in
    {
      bvar_bindings = (uu___423_4756.bvar_bindings);
      fvar_bindings = uu____4757;
      depth = (uu___423_4756.depth);
      tcenv = (uu___423_4756.tcenv);
      warn = (uu___423_4756.warn);
      nolabels = (uu___423_4756.nolabels);
      use_zfuel_name = (uu___423_4756.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___423_4756.encode_non_total_function_typ);
      current_module_name = (uu___423_4756.current_module_name);
      encoding_quantifier = (uu___423_4756.encoding_quantifier);
      global_cache = (uu___423_4756.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___428_4820 = env  in
      let uu____4821 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___428_4820.bvar_bindings);
        fvar_bindings = uu____4821;
        depth = (uu___428_4820.depth);
        tcenv = (uu___428_4820.tcenv);
        warn = (uu___428_4820.warn);
        nolabels = (uu___428_4820.nolabels);
        use_zfuel_name = (uu___428_4820.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___428_4820.encode_non_total_function_typ);
        current_module_name = (uu___428_4820.current_module_name);
        encoding_quantifier = (uu___428_4820.encoding_quantifier);
        global_cache = (uu___428_4820.global_cache)
      }
  