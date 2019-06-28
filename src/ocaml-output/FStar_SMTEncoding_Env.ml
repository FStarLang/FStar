open Prims
exception Inner_let_rec of (Prims.string * FStar_Range.range) 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec uu____44 -> true | uu____51 -> false
  
let (__proj__Inner_let_rec__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range)) =
  fun projectee  -> match projectee with | Inner_let_rec uu____69 -> uu____69 
let add_fuel :
  'Auu____82 . 'Auu____82 -> 'Auu____82 Prims.list -> 'Auu____82 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____99 = FStar_Options.unthrottle_inductives ()  in
      if uu____99 then tl1 else x :: tl1
  
let withenv :
  'Auu____117 'Auu____118 'Auu____119 .
    'Auu____117 ->
      ('Auu____118 * 'Auu____119) ->
        ('Auu____118 * 'Auu____119 * 'Auu____117)
  = fun c  -> fun uu____139  -> match uu____139 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____155 'Auu____156 'Auu____157 .
    (('Auu____155,'Auu____156) FStar_Util.either * 'Auu____157) Prims.list ->
      (('Auu____155,'Auu____156) FStar_Util.either * 'Auu____157) Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___0_204  ->
         match uu___0_204 with
         | (FStar_Util.Inl uu____214,uu____215) -> false
         | uu____221 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____254 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____254
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____284 =
          let uu____285 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____285  in
        let uu____289 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____289 with
        | (uu____295,t) ->
            let uu____297 =
              let uu____298 = FStar_Syntax_Subst.compress t  in
              uu____298.FStar_Syntax_Syntax.n  in
            (match uu____297 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____324 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____324 with
                  | (binders,uu____331) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____358 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____373 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____373
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____389 =
        let uu____390 =
          let uu____396 = mk_term_projector_name lid a  in
          (uu____396,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____390  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____389
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____412 =
        let uu____413 =
          let uu____419 = mk_term_projector_name_by_pos lid i  in
          (uu____419,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____413  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____412
  
let mk_data_tester :
  'Auu____431 .
    'Auu____431 ->
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
  let new_scope uu____1549 =
    let uu____1550 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____1556 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____1550, uu____1556)  in
  let scopes =
    let uu____1579 = let uu____1591 = new_scope ()  in [uu____1591]  in
    FStar_Util.mk_ref uu____1579  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1643 =
        let uu____1647 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1647
          (fun uu____1713  ->
             match uu____1713 with
             | (names1,uu____1727) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1643 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1741 ->
          (FStar_Util.incr ctr;
           (let uu____1745 =
              let uu____1747 =
                let uu____1749 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1749  in
              Prims.op_Hat "__" uu____1747  in
            Prims.op_Hat y1 uu____1745))
       in
    let top_scope =
      let uu____1777 =
        let uu____1787 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1787
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1777  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.op_Hat pp.FStar_Ident.idText
         (Prims.op_Hat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1899 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 mname pfx =
    let uu____1938 =
      let uu____1940 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1940  in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____1938  in
  let reset_fresh uu____1950 = FStar_ST.op_Colon_Equals ctr initial_ctr  in
  let string_const s =
    let uu____1980 =
      let uu____1983 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1983
        (fun uu____2048  ->
           match uu____2048 with
           | (uu____2060,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1980 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____2076 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2076  in
        let top_scope =
          let uu____2080 =
            let uu____2090 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____2090  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2080  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____2174 =
    let uu____2175 =
      let uu____2187 = new_scope ()  in
      let uu____2197 = FStar_ST.op_Bang scopes  in uu____2187 :: uu____2197
       in
    FStar_ST.op_Colon_Equals scopes uu____2175  in
  let pop1 uu____2305 =
    let uu____2306 =
      let uu____2318 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____2318
       in
    FStar_ST.op_Colon_Equals scopes uu____2306  in
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
    let term_opt_to_string uu___1_2642 =
      match uu___1_2642 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some s ->
          FStar_SMTEncoding_Term.print_smt_term s
       in
    let uu____2648 = FStar_Ident.string_of_lid fvb.fvar_lid  in
    let uu____2650 = term_opt_to_string fvb.smt_token  in
    let uu____2652 = term_opt_to_string fvb.smt_fuel_partial_app  in
    let uu____2654 = FStar_Util.string_of_bool fvb.fvb_thunked  in
    FStar_Util.format5
      "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }"
      uu____2648 fvb.smt_id uu____2650 uu____2652 uu____2654
  
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb  ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      (let uu____2665 =
         let uu____2667 = FStar_Ident.string_of_lid fvb.fvar_lid  in
         FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2667
          in
       failwith uu____2665)
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> (Prims.parse_int "0"))
      then
        (let uu____2675 =
           let uu____2677 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____2677
            in
         failwith uu____2675)
      else ();
    (match fvb.smt_token with
     | FStar_Pervasives_Native.Some
         {
           FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
             uu____2682;
           FStar_SMTEncoding_Term.freevars = uu____2683;
           FStar_SMTEncoding_Term.rng = uu____2684;_}
         ->
         let uu____2705 =
           let uu____2707 = fvb_to_string fvb  in
           FStar_Util.format1 "bad fvb\n%s" uu____2707  in
         failwith uu____2705
     | uu____2710 -> ())
  
let binder_of_eithervar :
  'Auu____2720 'Auu____2721 .
    'Auu____2720 ->
      ('Auu____2720 * 'Auu____2721 FStar_Pervasives_Native.option)
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
                    fun uu____3377  ->
                      fun acc1  ->
                        match uu____3377 with
                        | (x,_term) ->
                            let uu____3392 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3392 :: acc1) acc) []
       in
    let allvars =
      let uu____3399 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____3399
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3432 ->
          let uu____3435 = FStar_Syntax_Print.lid_to_string l  in
          Prims.op_Hat "...," uu____3435
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
      let uu____3457 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3457 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____3518 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____3518 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3542 .
    (FStar_Syntax_Syntax.bv * 'Auu____3542) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3542) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3542) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3602 =
             let uu____3609 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3609 pimap_opt  in
           FStar_Util.pimap_add uu____3602
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3656  ->
      match uu____3656 with
      | (fvb_map,fvb_list) ->
          let uu____3683 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____3683, (fvb :: fvb_list))
  
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
        let uu____3717 =
          let uu____3718 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3718  in
        (xsym, uu____3717)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____3743 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3743  in
      let uu____3745 =
        let uu___241_3746 = env  in
        let uu____3747 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3747;
          fvar_bindings = (uu___241_3746.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___241_3746.tcenv);
          warn = (uu___241_3746.warn);
          nolabels = (uu___241_3746.nolabels);
          use_zfuel_name = (uu___241_3746.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___241_3746.encode_non_total_function_typ);
          current_module_name = (uu___241_3746.current_module_name);
          encoding_quantifier = (uu___241_3746.encoding_quantifier);
          global_cache = (uu___241_3746.global_cache)
        }  in
      (ysym, y, uu____3745)
  
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
      let uu____3782 =
        let uu___247_3783 = env  in
        let uu____3784 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3784;
          fvar_bindings = (uu___247_3783.fvar_bindings);
          depth = (uu___247_3783.depth);
          tcenv = (uu___247_3783.tcenv);
          warn = (uu___247_3783.warn);
          nolabels = (uu___247_3783.nolabels);
          use_zfuel_name = (uu___247_3783.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___247_3783.encode_non_total_function_typ);
          current_module_name = (uu___247_3783.current_module_name);
          encoding_quantifier = (uu___247_3783.encoding_quantifier);
          global_cache = (uu___247_3783.global_cache)
        }  in
      (ysym, y, uu____3782)
  
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
        let uu____3825 =
          let uu___254_3826 = env  in
          let uu____3827 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3827;
            fvar_bindings = (uu___254_3826.fvar_bindings);
            depth = (uu___254_3826.depth);
            tcenv = (uu___254_3826.tcenv);
            warn = (uu___254_3826.warn);
            nolabels = (uu___254_3826.nolabels);
            use_zfuel_name = (uu___254_3826.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___254_3826.encode_non_total_function_typ);
            current_module_name = (uu___254_3826.current_module_name);
            encoding_quantifier = (uu___254_3826.encoding_quantifier);
            global_cache = (uu___254_3826.global_cache)
          }  in
        (ysym, y, uu____3825)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___259_3853 = env  in
        let uu____3854 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3854;
          fvar_bindings = (uu___259_3853.fvar_bindings);
          depth = (uu___259_3853.depth);
          tcenv = (uu___259_3853.tcenv);
          warn = (uu___259_3853.warn);
          nolabels = (uu___259_3853.nolabels);
          use_zfuel_name = (uu___259_3853.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___259_3853.encode_non_total_function_typ);
          current_module_name = (uu___259_3853.current_module_name);
          encoding_quantifier = (uu___259_3853.encoding_quantifier);
          global_cache = (uu___259_3853.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3874 = lookup_bvar_binding env a  in
      match uu____3874 with
      | FStar_Pervasives_Native.None  ->
          let uu____3885 = lookup_bvar_binding env a  in
          (match uu____3885 with
           | FStar_Pervasives_Native.None  ->
               let uu____3896 =
                 let uu____3898 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3900 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3898 uu____3900
                  in
               failwith uu____3896
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
          let uu____3999 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____3999 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____4063 =
                let uu___293_4064 = env  in
                let uu____4065 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___293_4064.bvar_bindings);
                  fvar_bindings = uu____4065;
                  depth = (uu___293_4064.depth);
                  tcenv = (uu___293_4064.tcenv);
                  warn = (uu___293_4064.warn);
                  nolabels = (uu___293_4064.nolabels);
                  use_zfuel_name = (uu___293_4064.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___293_4064.encode_non_total_function_typ);
                  current_module_name = (uu___293_4064.current_module_name);
                  encoding_quantifier = (uu___293_4064.encoding_quantifier);
                  global_cache = (uu___293_4064.global_cache)
                }  in
              (fname, ftok_name, uu____4063)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____4104 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____4104 with
        | (fname,ftok_name_opt,env1) ->
            let uu____4135 = FStar_Option.get ftok_name_opt  in
            (fname, uu____4135, env1)
  
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
      let uu____4186 = lookup_fvar_binding env a  in
      match uu____4186 with
      | FStar_Pervasives_Native.None  ->
          let uu____4189 =
            let uu____4191 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4191  in
          failwith uu____4189
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
              let uu___319_4238 = env  in
              let uu____4239 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___319_4238.bvar_bindings);
                fvar_bindings = uu____4239;
                depth = (uu___319_4238.depth);
                tcenv = (uu___319_4238.tcenv);
                warn = (uu___319_4238.warn);
                nolabels = (uu___319_4238.nolabels);
                use_zfuel_name = (uu___319_4238.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___319_4238.encode_non_total_function_typ);
                current_module_name = (uu___319_4238.current_module_name);
                encoding_quantifier = (uu___319_4238.encoding_quantifier);
                global_cache = (uu___319_4238.global_cache)
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
          let uu____4339 =
            let uu____4347 =
              let uu____4350 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4350]  in
            (f, uu____4347)  in
          FStar_SMTEncoding_Util.mkApp uu____4339  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___337_4360 = env  in
        let uu____4361 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___337_4360.bvar_bindings);
          fvar_bindings = uu____4361;
          depth = (uu___337_4360.depth);
          tcenv = (uu___337_4360.tcenv);
          warn = (uu___337_4360.warn);
          nolabels = (uu___337_4360.nolabels);
          use_zfuel_name = (uu___337_4360.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___337_4360.encode_non_total_function_typ);
          current_module_name = (uu___337_4360.current_module_name);
          encoding_quantifier = (uu___337_4360.encoding_quantifier);
          global_cache = (uu___337_4360.global_cache)
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
      let uu____4399 = lookup_fvar_binding env l  in
      match uu____4399 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          ((let uu____4406 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
                (FStar_Options.Other "PartialApp")
               in
            if uu____4406
            then
              let uu____4411 = FStar_Ident.string_of_lid l  in
              let uu____4413 = fvb_to_string fvb  in
              FStar_Util.print2 "Looked up %s found\n%s\n" uu____4411
                uu____4413
            else ());
           if fvb.fvb_thunked
           then
             (let uu____4421 = force_thunk fvb  in
              FStar_Pervasives_Native.Some uu____4421)
           else
             (match fvb.smt_fuel_partial_app with
              | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                  FStar_Pervasives_Native.Some f
              | uu____4427 ->
                  (match fvb.smt_token with
                   | FStar_Pervasives_Native.Some t ->
                       (match t.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App (uu____4435,fuel::[]) ->
                            let uu____4439 =
                              let uu____4441 =
                                let uu____4443 =
                                  FStar_SMTEncoding_Term.fv_of_term fuel  in
                                FStar_All.pipe_right uu____4443
                                  FStar_SMTEncoding_Term.fv_name
                                 in
                              FStar_Util.starts_with uu____4441 "fuel"  in
                            if uu____4439
                            then
                              let uu____4449 =
                                let uu____4450 =
                                  let uu____4451 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ((fvb.smt_id),
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Util.mkFreeV uu____4451
                                   in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu____4450
                                  fuel
                                 in
                              FStar_All.pipe_left
                                (fun _4455  ->
                                   FStar_Pervasives_Native.Some _4455)
                                uu____4449
                            else FStar_Pervasives_Native.Some t
                        | uu____4458 -> FStar_Pervasives_Native.Some t)
                   | uu____4459 -> FStar_Pervasives_Native.None)))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4477 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4477 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4481 =
            let uu____4483 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4483  in
          failwith uu____4481
  
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
            FStar_SMTEncoding_Term.freevars = uu____4545;
            FStar_SMTEncoding_Term.rng = uu____4546;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4571 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____4587 =
                 let uu____4592 = force_thunk fvb  in
                 FStar_Util.Inr uu____4592  in
               (uu____4587, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4633 ->
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
      let uu____4656 =
        let uu____4659 =
          FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
           in
        FStar_Util.psmap_find_map uu____4659
          (fun uu____4679  ->
             fun fvb  ->
               check_valid_fvb fvb;
               if fvb.smt_id = nm
               then fvb.smt_token
               else FStar_Pervasives_Native.None)
         in
      match uu____4656 with
      | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
      | FStar_Pervasives_Native.None  ->
          FStar_Util.psmap_find_map env.bvar_bindings
            (fun uu____4700  ->
               fun pi  ->
                 FStar_Util.pimap_fold pi
                   (fun uu____4720  ->
                      fun y  ->
                        fun res  ->
                          match (res, y) with
                          | (FStar_Pervasives_Native.Some
                             uu____4738,uu____4739) -> res
                          | (FStar_Pervasives_Native.None
                             ,(uu____4750,{
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Var
                                               sym,[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____4752;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____4753;_}))
                              when sym = nm ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.snd y)
                          | uu____4776 -> FStar_Pervasives_Native.None)
                   FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___424_4793 = env  in
    let uu____4794 =
      let uu____4803 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____4803, [])  in
    {
      bvar_bindings = (uu___424_4793.bvar_bindings);
      fvar_bindings = uu____4794;
      depth = (uu___424_4793.depth);
      tcenv = (uu___424_4793.tcenv);
      warn = (uu___424_4793.warn);
      nolabels = (uu___424_4793.nolabels);
      use_zfuel_name = (uu___424_4793.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___424_4793.encode_non_total_function_typ);
      current_module_name = (uu___424_4793.current_module_name);
      encoding_quantifier = (uu___424_4793.encoding_quantifier);
      global_cache = (uu___424_4793.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___429_4857 = env  in
      let uu____4858 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___429_4857.bvar_bindings);
        fvar_bindings = uu____4858;
        depth = (uu___429_4857.depth);
        tcenv = (uu___429_4857.tcenv);
        warn = (uu___429_4857.warn);
        nolabels = (uu___429_4857.nolabels);
        use_zfuel_name = (uu___429_4857.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___429_4857.encode_non_total_function_typ);
        current_module_name = (uu___429_4857.current_module_name);
        encoding_quantifier = (uu___429_4857.encoding_quantifier);
        global_cache = (uu___429_4857.global_cache)
      }
  