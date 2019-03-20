open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____62833 -> false
  
let add_fuel :
  'Auu____62842 .
    'Auu____62842 -> 'Auu____62842 Prims.list -> 'Auu____62842 Prims.list
  =
  fun x  ->
    fun tl1  ->
      let uu____62859 = FStar_Options.unthrottle_inductives ()  in
      if uu____62859 then tl1 else x :: tl1
  
let withenv :
  'Auu____62877 'Auu____62878 'Auu____62879 .
    'Auu____62877 ->
      ('Auu____62878 * 'Auu____62879) ->
        ('Auu____62878 * 'Auu____62879 * 'Auu____62877)
  = fun c  -> fun uu____62899  -> match uu____62899 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____62915 'Auu____62916 'Auu____62917 .
    (('Auu____62915,'Auu____62916) FStar_Util.either * 'Auu____62917)
      Prims.list ->
      (('Auu____62915,'Auu____62916) FStar_Util.either * 'Auu____62917)
        Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___596_62964  ->
         match uu___596_62964 with
         | (FStar_Util.Inl uu____62974,uu____62975) -> false
         | uu____62981 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____63014 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____63014
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____63044 =
          let uu____63045 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____63045  in
        let uu____63049 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____63049 with
        | (uu____63055,t) ->
            let uu____63057 =
              let uu____63058 = FStar_Syntax_Subst.compress t  in
              uu____63058.FStar_Syntax_Syntax.n  in
            (match uu____63057 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____63084 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____63084 with
                  | (binders,uu____63091) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____63118 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____63133 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____63133
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____63149 =
        let uu____63150 =
          let uu____63156 = mk_term_projector_name lid a  in
          (uu____63156,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____63150  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____63149
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____63172 =
        let uu____63173 =
          let uu____63179 = mk_term_projector_name_by_pos lid i  in
          (uu____63179,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____63173  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____63172
  
let mk_data_tester :
  'Auu____63191 .
    'Auu____63191 ->
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
  let new_scope uu____64309 =
    let uu____64310 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____64316 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____64310, uu____64316)  in
  let scopes =
    let uu____64339 = let uu____64351 = new_scope ()  in [uu____64351]  in
    FStar_Util.mk_ref uu____64339  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____64403 =
        let uu____64407 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____64407
          (fun uu____64473  ->
             match uu____64473 with
             | (names1,uu____64487) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____64403 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____64501 ->
          (FStar_Util.incr ctr;
           (let uu____64505 =
              let uu____64507 =
                let uu____64509 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____64509  in
              Prims.op_Hat "__" uu____64507  in
            Prims.op_Hat y1 uu____64505))
       in
    let top_scope =
      let uu____64537 =
        let uu____64547 = FStar_ST.op_Bang scopes  in
        FStar_List.hd uu____64547  in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____64537  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.op_Hat pp.FStar_Ident.idText
         (Prims.op_Hat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____64659 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 mname pfx =
    let uu____64698 =
      let uu____64700 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____64700  in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____64698  in
  let reset_fresh uu____64710 = FStar_ST.op_Colon_Equals ctr initial_ctr  in
  let string_const s =
    let uu____64740 =
      let uu____64743 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____64743
        (fun uu____64808  ->
           match uu____64808 with
           | (uu____64820,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____64740 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____64836 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____64836
           in
        let top_scope =
          let uu____64840 =
            let uu____64850 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____64850  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____64840  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____64934 =
    let uu____64935 =
      let uu____64947 = new_scope ()  in
      let uu____64957 = FStar_ST.op_Bang scopes  in uu____64947 ::
        uu____64957
       in
    FStar_ST.op_Colon_Equals scopes uu____64935  in
  let pop1 uu____65065 =
    let uu____65066 =
      let uu____65078 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____65078
       in
    FStar_ST.op_Colon_Equals scopes uu____65066  in
  let snapshot1 uu____65191 = FStar_Common.snapshot push1 scopes ()  in
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
      let uu____65394 =
        let uu____65396 = FStar_Ident.string_of_lid fvb.fvar_lid  in
        FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____65396
         in
      failwith uu____65394
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> (Prims.parse_int "0"))
      then
        (let uu____65404 =
           let uu____65406 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____65406
            in
         failwith uu____65404)
      else ()
  
let binder_of_eithervar :
  'Auu____65418 'Auu____65419 .
    'Auu____65418 ->
      ('Auu____65418 * 'Auu____65419 FStar_Pervasives_Native.option)
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
                    fun uu____66075  ->
                      fun acc1  ->
                        match uu____66075 with
                        | (x,_term) ->
                            let uu____66090 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____66090 :: acc1) acc) []
       in
    let allvars =
      let uu____66097 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____66097
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____66130 ->
          let uu____66133 = FStar_Syntax_Print.lid_to_string l  in
          Prims.op_Hat "...," uu____66133
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
      let uu____66155 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____66155 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____66216 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____66216 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____66240 .
    (FStar_Syntax_Syntax.bv * 'Auu____66240) ->
      (FStar_Syntax_Syntax.bv * 'Auu____66240) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____66240) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____66300 =
             let uu____66307 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____66307 pimap_opt  in
           FStar_Util.pimap_add uu____66300
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____66354  ->
      match uu____66354 with
      | (fvb_map,fvb_list) ->
          let uu____66381 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____66381, (fvb :: fvb_list))
  
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
        let uu____66415 =
          let uu____66416 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____66416  in
        (xsym, uu____66415)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____66441 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____66441  in
      let uu____66443 =
        let uu___821_66444 = env  in
        let uu____66445 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____66445;
          fvar_bindings = (uu___821_66444.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___821_66444.tcenv);
          warn = (uu___821_66444.warn);
          nolabels = (uu___821_66444.nolabels);
          use_zfuel_name = (uu___821_66444.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___821_66444.encode_non_total_function_typ);
          current_module_name = (uu___821_66444.current_module_name);
          encoding_quantifier = (uu___821_66444.encoding_quantifier);
          global_cache = (uu___821_66444.global_cache)
        }  in
      (ysym, y, uu____66443)
  
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
      let uu____66480 =
        let uu___827_66481 = env  in
        let uu____66482 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____66482;
          fvar_bindings = (uu___827_66481.fvar_bindings);
          depth = (uu___827_66481.depth);
          tcenv = (uu___827_66481.tcenv);
          warn = (uu___827_66481.warn);
          nolabels = (uu___827_66481.nolabels);
          use_zfuel_name = (uu___827_66481.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___827_66481.encode_non_total_function_typ);
          current_module_name = (uu___827_66481.current_module_name);
          encoding_quantifier = (uu___827_66481.encoding_quantifier);
          global_cache = (uu___827_66481.global_cache)
        }  in
      (ysym, y, uu____66480)
  
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
        let uu____66523 =
          let uu___834_66524 = env  in
          let uu____66525 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____66525;
            fvar_bindings = (uu___834_66524.fvar_bindings);
            depth = (uu___834_66524.depth);
            tcenv = (uu___834_66524.tcenv);
            warn = (uu___834_66524.warn);
            nolabels = (uu___834_66524.nolabels);
            use_zfuel_name = (uu___834_66524.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___834_66524.encode_non_total_function_typ);
            current_module_name = (uu___834_66524.current_module_name);
            encoding_quantifier = (uu___834_66524.encoding_quantifier);
            global_cache = (uu___834_66524.global_cache)
          }  in
        (ysym, y, uu____66523)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___839_66551 = env  in
        let uu____66552 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____66552;
          fvar_bindings = (uu___839_66551.fvar_bindings);
          depth = (uu___839_66551.depth);
          tcenv = (uu___839_66551.tcenv);
          warn = (uu___839_66551.warn);
          nolabels = (uu___839_66551.nolabels);
          use_zfuel_name = (uu___839_66551.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___839_66551.encode_non_total_function_typ);
          current_module_name = (uu___839_66551.current_module_name);
          encoding_quantifier = (uu___839_66551.encoding_quantifier);
          global_cache = (uu___839_66551.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____66572 = lookup_bvar_binding env a  in
      match uu____66572 with
      | FStar_Pervasives_Native.None  ->
          let uu____66583 = lookup_bvar_binding env a  in
          (match uu____66583 with
           | FStar_Pervasives_Native.None  ->
               let uu____66594 =
                 let uu____66596 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____66598 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____66596 uu____66598
                  in
               failwith uu____66594
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
          let uu____66697 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____66697 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____66761 =
                let uu___873_66762 = env  in
                let uu____66763 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___873_66762.bvar_bindings);
                  fvar_bindings = uu____66763;
                  depth = (uu___873_66762.depth);
                  tcenv = (uu___873_66762.tcenv);
                  warn = (uu___873_66762.warn);
                  nolabels = (uu___873_66762.nolabels);
                  use_zfuel_name = (uu___873_66762.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___873_66762.encode_non_total_function_typ);
                  current_module_name = (uu___873_66762.current_module_name);
                  encoding_quantifier = (uu___873_66762.encoding_quantifier);
                  global_cache = (uu___873_66762.global_cache)
                }  in
              (fname, ftok_name, uu____66761)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____66802 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____66802 with
        | (fname,ftok_name_opt,env1) ->
            let uu____66833 = FStar_Option.get ftok_name_opt  in
            (fname, uu____66833, env1)
  
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
      let uu____66884 = lookup_fvar_binding env a  in
      match uu____66884 with
      | FStar_Pervasives_Native.None  ->
          let uu____66887 =
            let uu____66889 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____66889  in
          failwith uu____66887
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
              let uu___899_66936 = env  in
              let uu____66937 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___899_66936.bvar_bindings);
                fvar_bindings = uu____66937;
                depth = (uu___899_66936.depth);
                tcenv = (uu___899_66936.tcenv);
                warn = (uu___899_66936.warn);
                nolabels = (uu___899_66936.nolabels);
                use_zfuel_name = (uu___899_66936.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___899_66936.encode_non_total_function_typ);
                current_module_name = (uu___899_66936.current_module_name);
                encoding_quantifier = (uu___899_66936.encoding_quantifier);
                global_cache = (uu___899_66936.global_cache)
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
          let uu____67037 =
            let uu____67045 =
              let uu____67048 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                 in
              [uu____67048]  in
            (f, uu____67045)  in
          FStar_SMTEncoding_Util.mkApp uu____67037  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___917_67058 = env  in
        let uu____67059 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___917_67058.bvar_bindings);
          fvar_bindings = uu____67059;
          depth = (uu___917_67058.depth);
          tcenv = (uu___917_67058.tcenv);
          warn = (uu___917_67058.warn);
          nolabels = (uu___917_67058.nolabels);
          use_zfuel_name = (uu___917_67058.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___917_67058.encode_non_total_function_typ);
          current_module_name = (uu___917_67058.current_module_name);
          encoding_quantifier = (uu___917_67058.encoding_quantifier);
          global_cache = (uu___917_67058.global_cache)
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
      let uu____67097 = lookup_fvar_binding env l  in
      match uu____67097 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          if fvb.fvb_thunked
          then
            let uu____67106 = force_thunk fvb  in
            FStar_Pervasives_Native.Some uu____67106
          else
            (match fvb.smt_fuel_partial_app with
             | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                 FStar_Pervasives_Native.Some f
             | uu____67112 ->
                 (match fvb.smt_token with
                  | FStar_Pervasives_Native.Some t ->
                      (match t.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App (uu____67120,fuel::[]) ->
                           let uu____67124 =
                             let uu____67126 =
                               let uu____67128 =
                                 FStar_SMTEncoding_Term.fv_of_term fuel  in
                               FStar_All.pipe_right uu____67128
                                 FStar_SMTEncoding_Term.fv_name
                                in
                             FStar_Util.starts_with uu____67126 "fuel"  in
                           if uu____67124
                           then
                             let uu____67134 =
                               let uu____67135 =
                                 let uu____67136 =
                                   FStar_SMTEncoding_Term.mk_fv
                                     ((fvb.smt_id),
                                       FStar_SMTEncoding_Term.Term_sort)
                                    in
                                 FStar_All.pipe_left
                                   FStar_SMTEncoding_Util.mkFreeV uu____67136
                                  in
                               FStar_SMTEncoding_Term.mk_ApplyTF uu____67135
                                 fuel
                                in
                             FStar_All.pipe_left
                               (fun _67140  ->
                                  FStar_Pervasives_Native.Some _67140)
                               uu____67134
                           else FStar_Pervasives_Native.Some t
                       | uu____67143 -> FStar_Pervasives_Native.Some t)
                  | uu____67144 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____67162 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____67162 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____67166 =
            let uu____67168 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____67168  in
          failwith uu____67166
  
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
            FStar_SMTEncoding_Term.freevars = uu____67230;
            FStar_SMTEncoding_Term.rng = uu____67231;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____67256 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____67272 =
                 let uu____67277 = force_thunk fvb  in
                 FStar_Util.Inr uu____67277  in
               (uu____67272, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____67318 ->
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
      let uu____67341 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_find_map uu____67341
        (fun uu____67361  ->
           fun fvb  ->
             check_valid_fvb fvb;
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___977_67377 = env  in
    let uu____67378 =
      let uu____67387 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____67387, [])  in
    {
      bvar_bindings = (uu___977_67377.bvar_bindings);
      fvar_bindings = uu____67378;
      depth = (uu___977_67377.depth);
      tcenv = (uu___977_67377.tcenv);
      warn = (uu___977_67377.warn);
      nolabels = (uu___977_67377.nolabels);
      use_zfuel_name = (uu___977_67377.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___977_67377.encode_non_total_function_typ);
      current_module_name = (uu___977_67377.current_module_name);
      encoding_quantifier = (uu___977_67377.encoding_quantifier);
      global_cache = (uu___977_67377.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___982_67441 = env  in
      let uu____67442 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___982_67441.bvar_bindings);
        fvar_bindings = uu____67442;
        depth = (uu___982_67441.depth);
        tcenv = (uu___982_67441.tcenv);
        warn = (uu___982_67441.warn);
        nolabels = (uu___982_67441.nolabels);
        use_zfuel_name = (uu___982_67441.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___982_67441.encode_non_total_function_typ);
        current_module_name = (uu___982_67441.current_module_name);
        encoding_quantifier = (uu___982_67441.encoding_quantifier);
        global_cache = (uu___982_67441.global_cache)
      }
  