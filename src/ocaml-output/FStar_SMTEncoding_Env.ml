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
      (fun uu___33_140  ->
         match uu___33_140 with
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
                    fun uu____3298  ->
                      fun acc1  ->
                        match uu____3298 with
                        | (x,_term) ->
                            let uu____3313 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3313 :: acc1) acc) []
       in
    let allvars =
      let uu____3320 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____3320
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3353 ->
          let uu____3356 = FStar_Syntax_Print.lid_to_string l  in
          Prims.strcat "...," uu____3356
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
      let uu____3378 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____3378 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____3439 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____3439 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____3463 .
    (FStar_Syntax_Syntax.bv * 'Auu____3463) ->
      (FStar_Syntax_Syntax.bv * 'Auu____3463) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____3463) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____3523 =
             let uu____3530 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3530 pimap_opt  in
           FStar_Util.pimap_add uu____3523
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3577  ->
      match uu____3577 with
      | (fvb_map,fvb_list) ->
          let uu____3604 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____3604, (fvb :: fvb_list))
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string * FStar_SMTEncoding_Term.term))
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____3631 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____3631)
  
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
      let uu____3657 =
        let uu___34_3658 = env  in
        let uu____3659 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3659;
          fvar_bindings = (uu___34_3658.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___34_3658.tcenv);
          warn = (uu___34_3658.warn);
          nolabels = (uu___34_3658.nolabels);
          use_zfuel_name = (uu___34_3658.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___34_3658.encode_non_total_function_typ);
          current_module_name = (uu___34_3658.current_module_name);
          encoding_quantifier = (uu___34_3658.encoding_quantifier);
          global_cache = (uu___34_3658.global_cache)
        }  in
      (ysym, y, uu____3657)
  
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
      let uu____3694 =
        let uu___35_3695 = env  in
        let uu____3696 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3696;
          fvar_bindings = (uu___35_3695.fvar_bindings);
          depth = (uu___35_3695.depth);
          tcenv = (uu___35_3695.tcenv);
          warn = (uu___35_3695.warn);
          nolabels = (uu___35_3695.nolabels);
          use_zfuel_name = (uu___35_3695.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___35_3695.encode_non_total_function_typ);
          current_module_name = (uu___35_3695.current_module_name);
          encoding_quantifier = (uu___35_3695.encoding_quantifier);
          global_cache = (uu___35_3695.global_cache)
        }  in
      (ysym, y, uu____3694)
  
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
        let uu____3737 =
          let uu___36_3738 = env  in
          let uu____3739 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3739;
            fvar_bindings = (uu___36_3738.fvar_bindings);
            depth = (uu___36_3738.depth);
            tcenv = (uu___36_3738.tcenv);
            warn = (uu___36_3738.warn);
            nolabels = (uu___36_3738.nolabels);
            use_zfuel_name = (uu___36_3738.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___36_3738.encode_non_total_function_typ);
            current_module_name = (uu___36_3738.current_module_name);
            encoding_quantifier = (uu___36_3738.encoding_quantifier);
            global_cache = (uu___36_3738.global_cache)
          }  in
        (ysym, y, uu____3737)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___37_3765 = env  in
        let uu____3766 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3766;
          fvar_bindings = (uu___37_3765.fvar_bindings);
          depth = (uu___37_3765.depth);
          tcenv = (uu___37_3765.tcenv);
          warn = (uu___37_3765.warn);
          nolabels = (uu___37_3765.nolabels);
          use_zfuel_name = (uu___37_3765.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___37_3765.encode_non_total_function_typ);
          current_module_name = (uu___37_3765.current_module_name);
          encoding_quantifier = (uu___37_3765.encoding_quantifier);
          global_cache = (uu___37_3765.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3786 = lookup_bvar_binding env a  in
      match uu____3786 with
      | FStar_Pervasives_Native.None  ->
          let uu____3797 = lookup_bvar_binding env a  in
          (match uu____3797 with
           | FStar_Pervasives_Native.None  ->
               let uu____3808 =
                 let uu____3810 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3812 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3810 uu____3812
                  in
               failwith uu____3808
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
        let uu____3901 =
          let uu___38_3902 = env  in
          let uu____3903 = add_fvar_binding fvb env.fvar_bindings  in
          {
            bvar_bindings = (uu___38_3902.bvar_bindings);
            fvar_bindings = uu____3903;
            depth = (uu___38_3902.depth);
            tcenv = (uu___38_3902.tcenv);
            warn = (uu___38_3902.warn);
            nolabels = (uu___38_3902.nolabels);
            use_zfuel_name = (uu___38_3902.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___38_3902.encode_non_total_function_typ);
            current_module_name = (uu___38_3902.current_module_name);
            encoding_quantifier = (uu___38_3902.encoding_quantifier);
            global_cache = (uu___38_3902.global_cache)
          }  in
        (fname, ftok_name, uu____3901)
  
let (lookup_lid : env_t -> FStar_Ident.lident -> fvar_binding) =
  fun env  ->
    fun a  ->
      let uu____3925 = lookup_fvar_binding env a  in
      match uu____3925 with
      | FStar_Pervasives_Native.None  ->
          let uu____3928 =
            let uu____3930 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____3930  in
          failwith uu____3928
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
            let uu___39_3969 = env  in
            let uu____3970 = add_fvar_binding fvb env.fvar_bindings  in
            {
              bvar_bindings = (uu___39_3969.bvar_bindings);
              fvar_bindings = uu____3970;
              depth = (uu___39_3969.depth);
              tcenv = (uu___39_3969.tcenv);
              warn = (uu___39_3969.warn);
              nolabels = (uu___39_3969.nolabels);
              use_zfuel_name = (uu___39_3969.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___39_3969.encode_non_total_function_typ);
              current_module_name = (uu___39_3969.current_module_name);
              encoding_quantifier = (uu___39_3969.encoding_quantifier);
              global_cache = (uu___39_3969.global_cache)
            }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____3999 =
            let uu____4007 =
              let uu____4010 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4010]  in
            (f, uu____4007)  in
          FStar_SMTEncoding_Util.mkApp uu____3999  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3)
           in
        let uu___40_4019 = env  in
        let uu____4020 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___40_4019.bvar_bindings);
          fvar_bindings = uu____4020;
          depth = (uu___40_4019.depth);
          tcenv = (uu___40_4019.tcenv);
          warn = (uu___40_4019.warn);
          nolabels = (uu___40_4019.nolabels);
          use_zfuel_name = (uu___40_4019.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___40_4019.encode_non_total_function_typ);
          current_module_name = (uu___40_4019.current_module_name);
          encoding_quantifier = (uu___40_4019.encoding_quantifier);
          global_cache = (uu___40_4019.global_cache)
        }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____4042 = lookup_fvar_binding env l  in
      match uu____4042 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          (match fvb.smt_fuel_partial_app with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____4051 ->
               (match fvb.smt_token with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____4059,fuel::[]) ->
                         let uu____4063 =
                           let uu____4065 =
                             let uu____4067 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____4067
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____4065 "fuel"  in
                         if uu____4063
                         then
                           let uu____4084 =
                             let uu____4085 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 ((fvb.smt_id),
                                   FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____4085
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_1  -> FStar_Pervasives_Native.Some _0_1)
                             uu____4084
                         else FStar_Pervasives_Native.Some t
                     | uu____4091 -> FStar_Pervasives_Native.Some t)
                | uu____4092 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4110 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4110 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4114 =
            let uu____4116 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4116  in
          failwith uu____4114
  
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
            FStar_SMTEncoding_Term.freevars = uu____4179;
            FStar_SMTEncoding_Term.rng = uu____4180;_}
          when env.use_zfuel_name ->
          (g, zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____4198 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  ->
               ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                 (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    (g, [fuel], (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____4231 ->
                    ((FStar_SMTEncoding_Term.Var (fvb.smt_id)), [],
                      (fvb.smt_arity))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      let uu____4250 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_find_map uu____4250
        (fun uu____4269  ->
           fun fvb  ->
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___41_4284 = env  in
    let uu____4285 =
      let uu____4294 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____4294, [])  in
    {
      bvar_bindings = (uu___41_4284.bvar_bindings);
      fvar_bindings = uu____4285;
      depth = (uu___41_4284.depth);
      tcenv = (uu___41_4284.tcenv);
      warn = (uu___41_4284.warn);
      nolabels = (uu___41_4284.nolabels);
      use_zfuel_name = (uu___41_4284.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___41_4284.encode_non_total_function_typ);
      current_module_name = (uu___41_4284.current_module_name);
      encoding_quantifier = (uu___41_4284.encoding_quantifier);
      global_cache = (uu___41_4284.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___42_4348 = env  in
      let uu____4349 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___42_4348.bvar_bindings);
        fvar_bindings = uu____4349;
        depth = (uu___42_4348.depth);
        tcenv = (uu___42_4348.tcenv);
        warn = (uu___42_4348.warn);
        nolabels = (uu___42_4348.nolabels);
        use_zfuel_name = (uu___42_4348.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___42_4348.encode_non_total_function_typ);
        current_module_name = (uu___42_4348.current_module_name);
        encoding_quantifier = (uu___42_4348.encoding_quantifier);
        global_cache = (uu___42_4348.global_cache)
      }
  