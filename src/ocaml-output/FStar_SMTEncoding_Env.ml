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
      (fun uu___11_140  ->
         match uu___11_140 with
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
        let uu____326 =
          let uu____332 = mk_term_projector_name lid a  in
          (uu____332,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____326  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____325
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____348 =
        let uu____349 =
          let uu____355 = mk_term_projector_name_by_pos lid i  in
          (uu____355,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____349  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____348
  
let mk_data_tester :
  'Auu____367 .
    'Auu____367 ->
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
  let new_scope uu____1485 =
    let uu____1486 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____1492 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____1486, uu____1492)  in
  let scopes =
    let uu____1515 = let uu____1527 = new_scope ()  in [uu____1527]  in
    FStar_Util.mk_ref uu____1515  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1579 =
        let uu____1583 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1583
          (fun uu____1671  ->
             match uu____1671 with
             | (names1,uu____1685) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____1579 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1699 ->
          (FStar_Util.incr ctr;
           (let uu____1736 =
              let uu____1738 =
                let uu____1740 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1740  in
              Prims.strcat "__" uu____1738  in
            Prims.strcat y1 uu____1736))
       in
    let top_scope =
      let uu____1790 =
        let uu____1800 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1800
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1790  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1934 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 mname pfx =
    let uu____2028 =
      let uu____2030 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____2030  in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____2028  in
  let reset_fresh uu____2040 = FStar_ST.op_Colon_Equals ctr initial_ctr  in
  let string_const s =
    let uu____2092 =
      let uu____2095 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____2095
        (fun uu____2182  ->
           match uu____2182 with
           | (uu____2194,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____2092 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____2210 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2210  in
        let top_scope =
          let uu____2214 =
            let uu____2224 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____2224  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2214  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____2330 =
    let uu____2331 =
      let uu____2343 = new_scope ()  in
      let uu____2353 = FStar_ST.op_Bang scopes  in uu____2343 :: uu____2353
       in
    FStar_ST.op_Colon_Equals scopes uu____2331  in
  let pop1 uu____2505 =
    let uu____2506 =
      let uu____2518 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____2518
       in
    FStar_ST.op_Colon_Equals scopes uu____2506  in
  let snapshot1 uu____2675 = FStar_Common.snapshot push1 scopes ()  in
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
      let uu____2922 =
        let uu____2924 = FStar_Ident.string_of_lid fvb.fvar_lid  in
        FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2924  in
      failwith uu____2922
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> (Prims.parse_int "0"))
      then
        (let uu____2932 =
           let uu____2934 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____2934
            in
         failwith uu____2932)
      else ()
  
let binder_of_eithervar :
  'Auu____2946 'Auu____2947 .
    'Auu____2946 ->
      ('Auu____2946 * 'Auu____2947 FStar_Pervasives_Native.option)
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
                    fun uu____3603  ->
                      fun acc1  ->
                        match uu____3603 with
                        | (x,_term) ->
                            let uu____3618 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3618 :: acc1) acc) []
       in
    let allvars =
      let uu____3625 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____3625
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3658 ->
          let uu____3661 = FStar_Syntax_Print.lid_to_string l  in
          Prims.strcat "...," uu____3661
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
      let uu____3683 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3683 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____3744 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____3744 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3768 .
    (FStar_Syntax_Syntax.bv * 'Auu____3768) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3768) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3768) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3828 =
             let uu____3835 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3835 pimap_opt  in
           FStar_Util.pimap_add uu____3828
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3882  ->
      match uu____3882 with
      | (fvb_map,fvb_list) ->
          let uu____3909 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____3909, (fvb :: fvb_list))
  
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
        let uu____3943 =
          let uu____3944 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3944  in
        (xsym, uu____3943)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____3969 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3969  in
      let uu____3971 =
        let uu___12_3972 = env  in
        let uu____3973 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3973;
          fvar_bindings = (uu___12_3972.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___12_3972.tcenv);
          warn = (uu___12_3972.warn);
          nolabels = (uu___12_3972.nolabels);
          use_zfuel_name = (uu___12_3972.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___12_3972.encode_non_total_function_typ);
          current_module_name = (uu___12_3972.current_module_name);
          encoding_quantifier = (uu___12_3972.encoding_quantifier);
          global_cache = (uu___12_3972.global_cache)
        }  in
      (ysym, y, uu____3971)
  
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
      let uu____4008 =
        let uu___13_4009 = env  in
        let uu____4010 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____4010;
          fvar_bindings = (uu___13_4009.fvar_bindings);
          depth = (uu___13_4009.depth);
          tcenv = (uu___13_4009.tcenv);
          warn = (uu___13_4009.warn);
          nolabels = (uu___13_4009.nolabels);
          use_zfuel_name = (uu___13_4009.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___13_4009.encode_non_total_function_typ);
          current_module_name = (uu___13_4009.current_module_name);
          encoding_quantifier = (uu___13_4009.encoding_quantifier);
          global_cache = (uu___13_4009.global_cache)
        }  in
      (ysym, y, uu____4008)
  
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
        let uu____4051 =
          let uu___14_4052 = env  in
          let uu____4053 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____4053;
            fvar_bindings = (uu___14_4052.fvar_bindings);
            depth = (uu___14_4052.depth);
            tcenv = (uu___14_4052.tcenv);
            warn = (uu___14_4052.warn);
            nolabels = (uu___14_4052.nolabels);
            use_zfuel_name = (uu___14_4052.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___14_4052.encode_non_total_function_typ);
            current_module_name = (uu___14_4052.current_module_name);
            encoding_quantifier = (uu___14_4052.encoding_quantifier);
            global_cache = (uu___14_4052.global_cache)
          }  in
        (ysym, y, uu____4051)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___15_4079 = env  in
        let uu____4080 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____4080;
          fvar_bindings = (uu___15_4079.fvar_bindings);
          depth = (uu___15_4079.depth);
          tcenv = (uu___15_4079.tcenv);
          warn = (uu___15_4079.warn);
          nolabels = (uu___15_4079.nolabels);
          use_zfuel_name = (uu___15_4079.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___15_4079.encode_non_total_function_typ);
          current_module_name = (uu___15_4079.current_module_name);
          encoding_quantifier = (uu___15_4079.encoding_quantifier);
          global_cache = (uu___15_4079.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____4100 = lookup_bvar_binding env a  in
      match uu____4100 with
      | FStar_Pervasives_Native.None  ->
          let uu____4111 = lookup_bvar_binding env a  in
          (match uu____4111 with
           | FStar_Pervasives_Native.None  ->
               let uu____4122 =
                 let uu____4124 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____4126 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____4124 uu____4126
                  in
               failwith uu____4122
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
          let uu____4225 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.strcat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____4225 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____4289 =
                let uu___16_4290 = env  in
                let uu____4291 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___16_4290.bvar_bindings);
                  fvar_bindings = uu____4291;
                  depth = (uu___16_4290.depth);
                  tcenv = (uu___16_4290.tcenv);
                  warn = (uu___16_4290.warn);
                  nolabels = (uu___16_4290.nolabels);
                  use_zfuel_name = (uu___16_4290.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___16_4290.encode_non_total_function_typ);
                  current_module_name = (uu___16_4290.current_module_name);
                  encoding_quantifier = (uu___16_4290.encoding_quantifier);
                  global_cache = (uu___16_4290.global_cache)
                }  in
              (fname, ftok_name, uu____4289)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____4330 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____4330 with
        | (fname,ftok_name_opt,env1) ->
            let uu____4361 = FStar_Option.get ftok_name_opt  in
            (fname, uu____4361, env1)
  
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
      let uu____4412 = lookup_fvar_binding env a  in
      match uu____4412 with
      | FStar_Pervasives_Native.None  ->
          let uu____4415 =
            let uu____4417 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4417  in
          failwith uu____4415
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
              let uu___17_4464 = env  in
              let uu____4465 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___17_4464.bvar_bindings);
                fvar_bindings = uu____4465;
                depth = (uu___17_4464.depth);
                tcenv = (uu___17_4464.tcenv);
                warn = (uu___17_4464.warn);
                nolabels = (uu___17_4464.nolabels);
                use_zfuel_name = (uu___17_4464.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___17_4464.encode_non_total_function_typ);
                current_module_name = (uu___17_4464.current_module_name);
                encoding_quantifier = (uu___17_4464.encoding_quantifier);
                global_cache = (uu___17_4464.global_cache)
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
          let uu____4565 =
            let uu____4573 =
              let uu____4576 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4576]  in
            (f, uu____4573)  in
          FStar_SMTEncoding_Util.mkApp uu____4565  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___18_4586 = env  in
        let uu____4587 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___18_4586.bvar_bindings);
          fvar_bindings = uu____4587;
          depth = (uu___18_4586.depth);
          tcenv = (uu___18_4586.tcenv);
          warn = (uu___18_4586.warn);
          nolabels = (uu___18_4586.nolabels);
          use_zfuel_name = (uu___18_4586.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___18_4586.encode_non_total_function_typ);
          current_module_name = (uu___18_4586.current_module_name);
          encoding_quantifier = (uu___18_4586.encoding_quantifier);
          global_cache = (uu___18_4586.global_cache)
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
      let uu____4625 = lookup_fvar_binding env l  in
      match uu____4625 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          if fvb.fvb_thunked
          then
            let uu____4634 = force_thunk fvb  in
            FStar_Pervasives_Native.Some uu____4634
          else
            (match fvb.smt_fuel_partial_app with
             | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                 FStar_Pervasives_Native.Some f
             | uu____4640 ->
                 (match fvb.smt_token with
                  | FStar_Pervasives_Native.Some t ->
                      (match t.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App (uu____4648,fuel::[]) ->
                           let uu____4652 =
                             let uu____4654 =
                               let uu____4656 =
                                 FStar_SMTEncoding_Term.fv_of_term fuel  in
                               FStar_All.pipe_right uu____4656
                                 FStar_SMTEncoding_Term.fv_name
                                in
                             FStar_Util.starts_with uu____4654 "fuel"  in
                           if uu____4652
                           then
                             let uu____4662 =
                               let uu____4663 =
                                 let uu____4664 =
                                   FStar_SMTEncoding_Term.mk_fv
                                     ((fvb.smt_id),
                                       FStar_SMTEncoding_Term.Term_sort)
                                    in
                                 FStar_All.pipe_left
                                   FStar_SMTEncoding_Util.mkFreeV uu____4664
                                  in
                               FStar_SMTEncoding_Term.mk_ApplyTF uu____4663
                                 fuel
                                in
                             FStar_All.pipe_left
                               (fun _0_1  ->
                                  FStar_Pervasives_Native.Some _0_1)
                               uu____4662
                           else FStar_Pervasives_Native.Some t
                       | uu____4670 -> FStar_Pervasives_Native.Some t)
                  | uu____4671 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4689 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4689 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4693 =
            let uu____4695 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4695  in
          failwith uu____4693
  
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
            FStar_SMTEncoding_Term.freevars = uu____4757;
            FStar_SMTEncoding_Term.rng = uu____4758;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4783 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____4799 =
                 let uu____4804 = force_thunk fvb  in
                 FStar_Util.Inr uu____4804  in
               (uu____4799, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4845 ->
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
      let uu____4868 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_find_map uu____4868
        (fun uu____4888  ->
           fun fvb  ->
             check_valid_fvb fvb;
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___19_4904 = env  in
    let uu____4905 =
      let uu____4914 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____4914, [])  in
    {
      bvar_bindings = (uu___19_4904.bvar_bindings);
      fvar_bindings = uu____4905;
      depth = (uu___19_4904.depth);
      tcenv = (uu___19_4904.tcenv);
      warn = (uu___19_4904.warn);
      nolabels = (uu___19_4904.nolabels);
      use_zfuel_name = (uu___19_4904.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___19_4904.encode_non_total_function_typ);
      current_module_name = (uu___19_4904.current_module_name);
      encoding_quantifier = (uu___19_4904.encoding_quantifier);
      global_cache = (uu___19_4904.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___20_4968 = env  in
      let uu____4969 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___20_4968.bvar_bindings);
        fvar_bindings = uu____4969;
        depth = (uu___20_4968.depth);
        tcenv = (uu___20_4968.tcenv);
        warn = (uu___20_4968.warn);
        nolabels = (uu___20_4968.nolabels);
        use_zfuel_name = (uu___20_4968.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___20_4968.encode_non_total_function_typ);
        current_module_name = (uu___20_4968.current_module_name);
        encoding_quantifier = (uu___20_4968.encoding_quantifier);
        global_cache = (uu___20_4968.global_cache)
      }
  