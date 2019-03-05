open Prims
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____67745 -> false
  
let add_fuel :
  'Auu____67754 .
    'Auu____67754 -> 'Auu____67754 Prims.list -> 'Auu____67754 Prims.list
  =
  fun x  ->
    fun tl1  ->
      let uu____67771 = FStar_Options.unthrottle_inductives ()  in
      if uu____67771 then tl1 else x :: tl1
  
let withenv :
  'Auu____67789 'Auu____67790 'Auu____67791 .
    'Auu____67789 ->
      ('Auu____67790 * 'Auu____67791) ->
        ('Auu____67790 * 'Auu____67791 * 'Auu____67789)
  = fun c  -> fun uu____67811  -> match uu____67811 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____67827 'Auu____67828 'Auu____67829 .
    (('Auu____67827,'Auu____67828) FStar_Util.either * 'Auu____67829)
      Prims.list ->
      (('Auu____67827,'Auu____67828) FStar_Util.either * 'Auu____67829)
        Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___596_67876  ->
         match uu___596_67876 with
         | (FStar_Util.Inl uu____67886,uu____67887) -> false
         | uu____67893 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____67926 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____67926
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail1 uu____67956 =
          let uu____67957 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____67957  in
        let uu____67961 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____67961 with
        | (uu____67967,t) ->
            let uu____67969 =
              let uu____67970 = FStar_Syntax_Subst.compress t  in
              uu____67970.FStar_Syntax_Syntax.n  in
            (match uu____67969 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____67996 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____67996 with
                  | (binders,uu____68003) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail1 ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____68030 -> fail1 ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____68045 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____68045
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____68061 =
        let uu____68062 =
          let uu____68068 = mk_term_projector_name lid a  in
          (uu____68068,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____68062  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____68061
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____68084 =
        let uu____68085 =
          let uu____68091 = mk_term_projector_name_by_pos lid i  in
          (uu____68091,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____68085  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____68084
  
let mk_data_tester :
  'Auu____68103 .
    'Auu____68103 ->
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
  let new_scope uu____69221 =
    let uu____69222 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____69228 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____69222, uu____69228)  in
  let scopes =
    let uu____69251 = let uu____69263 = new_scope ()  in [uu____69263]  in
    FStar_Util.mk_ref uu____69251  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____69315 =
        let uu____69319 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____69319
          (fun uu____69407  ->
             match uu____69407 with
             | (names1,uu____69421) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____69315 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____69435 ->
          (FStar_Util.incr ctr;
           (let uu____69472 =
              let uu____69474 =
                let uu____69476 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____69476  in
              Prims.op_Hat "__" uu____69474  in
            Prims.op_Hat y1 uu____69472))
       in
    let top_scope =
      let uu____69526 =
        let uu____69536 = FStar_ST.op_Bang scopes  in
        FStar_List.hd uu____69536  in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____69526  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.op_Hat pp.FStar_Ident.idText
         (Prims.op_Hat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____69670 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 mname pfx =
    let uu____69764 =
      let uu____69766 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____69766  in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____69764  in
  let reset_fresh uu____69776 = FStar_ST.op_Colon_Equals ctr initial_ctr  in
  let string_const s =
    let uu____69828 =
      let uu____69831 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____69831
        (fun uu____69918  ->
           match uu____69918 with
           | (uu____69930,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____69828 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____69946 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____69946
           in
        let top_scope =
          let uu____69950 =
            let uu____69960 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____69960  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____69950  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____70066 =
    let uu____70067 =
      let uu____70079 = new_scope ()  in
      let uu____70089 = FStar_ST.op_Bang scopes  in uu____70079 ::
        uu____70089
       in
    FStar_ST.op_Colon_Equals scopes uu____70067  in
  let pop1 uu____70241 =
    let uu____70242 =
      let uu____70254 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____70254
       in
    FStar_ST.op_Colon_Equals scopes uu____70242  in
  let snapshot1 uu____70411 = FStar_Common.snapshot push1 scopes ()  in
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
      let uu____70658 =
        let uu____70660 = FStar_Ident.string_of_lid fvb.fvar_lid  in
        FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____70660
         in
      failwith uu____70658
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> (Prims.parse_int "0"))
      then
        (let uu____70668 =
           let uu____70670 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____70670
            in
         failwith uu____70668)
      else ()
  
let binder_of_eithervar :
  'Auu____70682 'Auu____70683 .
    'Auu____70682 ->
      ('Auu____70682 * 'Auu____70683 FStar_Pervasives_Native.option)
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
                    fun uu____71339  ->
                      fun acc1  ->
                        match uu____71339 with
                        | (x,_term) ->
                            let uu____71354 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____71354 :: acc1) acc) []
       in
    let allvars =
      let uu____71361 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____71361
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____71394 ->
          let uu____71397 = FStar_Syntax_Print.lid_to_string l  in
          Prims.op_Hat "...," uu____71397
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
      let uu____71419 =
        FStar_Util.psmap_try_find env.bvar_bindings
          (bv.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      match uu____71419 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____71480 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_try_find uu____71480 lid.FStar_Ident.str
  
let add_bvar_binding :
  'Auu____71504 .
    (FStar_Syntax_Syntax.bv * 'Auu____71504) ->
      (FStar_Syntax_Syntax.bv * 'Auu____71504) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'Auu____71504) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      FStar_Util.psmap_modify bvbs
        ((FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname).FStar_Ident.idText
        (fun pimap_opt  ->
           let uu____71564 =
             let uu____71571 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____71571 pimap_opt  in
           FStar_Util.pimap_add uu____71564
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____71618  ->
      match uu____71618 with
      | (fvb_map,fvb_list) ->
          let uu____71645 =
            FStar_Util.psmap_add fvb_map (fvb.fvar_lid).FStar_Ident.str fvb
             in
          (uu____71645, (fvb :: fvb_list))
  
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
        let uu____71679 =
          let uu____71680 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71680  in
        (xsym, uu____71679)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____71705 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____71705  in
      let uu____71707 =
        let uu___821_71708 = env  in
        let uu____71709 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____71709;
          fvar_bindings = (uu___821_71708.fvar_bindings);
          depth = (env.depth + (Prims.parse_int "1"));
          tcenv = (uu___821_71708.tcenv);
          warn = (uu___821_71708.warn);
          nolabels = (uu___821_71708.nolabels);
          use_zfuel_name = (uu___821_71708.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___821_71708.encode_non_total_function_typ);
          current_module_name = (uu___821_71708.current_module_name);
          encoding_quantifier = (uu___821_71708.encoding_quantifier);
          global_cache = (uu___821_71708.global_cache)
        }  in
      (ysym, y, uu____71707)
  
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
      let uu____71744 =
        let uu___827_71745 = env  in
        let uu____71746 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____71746;
          fvar_bindings = (uu___827_71745.fvar_bindings);
          depth = (uu___827_71745.depth);
          tcenv = (uu___827_71745.tcenv);
          warn = (uu___827_71745.warn);
          nolabels = (uu___827_71745.nolabels);
          use_zfuel_name = (uu___827_71745.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___827_71745.encode_non_total_function_typ);
          current_module_name = (uu___827_71745.current_module_name);
          encoding_quantifier = (uu___827_71745.encoding_quantifier);
          global_cache = (uu___827_71745.global_cache)
        }  in
      (ysym, y, uu____71744)
  
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
        let uu____71787 =
          let uu___834_71788 = env  in
          let uu____71789 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____71789;
            fvar_bindings = (uu___834_71788.fvar_bindings);
            depth = (uu___834_71788.depth);
            tcenv = (uu___834_71788.tcenv);
            warn = (uu___834_71788.warn);
            nolabels = (uu___834_71788.nolabels);
            use_zfuel_name = (uu___834_71788.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___834_71788.encode_non_total_function_typ);
            current_module_name = (uu___834_71788.current_module_name);
            encoding_quantifier = (uu___834_71788.encoding_quantifier);
            global_cache = (uu___834_71788.global_cache)
          }  in
        (ysym, y, uu____71787)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___839_71815 = env  in
        let uu____71816 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____71816;
          fvar_bindings = (uu___839_71815.fvar_bindings);
          depth = (uu___839_71815.depth);
          tcenv = (uu___839_71815.tcenv);
          warn = (uu___839_71815.warn);
          nolabels = (uu___839_71815.nolabels);
          use_zfuel_name = (uu___839_71815.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___839_71815.encode_non_total_function_typ);
          current_module_name = (uu___839_71815.current_module_name);
          encoding_quantifier = (uu___839_71815.encoding_quantifier);
          global_cache = (uu___839_71815.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____71836 = lookup_bvar_binding env a  in
      match uu____71836 with
      | FStar_Pervasives_Native.None  ->
          let uu____71847 = lookup_bvar_binding env a  in
          (match uu____71847 with
           | FStar_Pervasives_Native.None  ->
               let uu____71858 =
                 let uu____71860 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____71862 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____71860 uu____71862
                  in
               failwith uu____71858
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
          let uu____71961 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____71961 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____72025 =
                let uu___873_72026 = env  in
                let uu____72027 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___873_72026.bvar_bindings);
                  fvar_bindings = uu____72027;
                  depth = (uu___873_72026.depth);
                  tcenv = (uu___873_72026.tcenv);
                  warn = (uu___873_72026.warn);
                  nolabels = (uu___873_72026.nolabels);
                  use_zfuel_name = (uu___873_72026.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___873_72026.encode_non_total_function_typ);
                  current_module_name = (uu___873_72026.current_module_name);
                  encoding_quantifier = (uu___873_72026.encoding_quantifier);
                  global_cache = (uu___873_72026.global_cache)
                }  in
              (fname, ftok_name, uu____72025)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____72066 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____72066 with
        | (fname,ftok_name_opt,env1) ->
            let uu____72097 = FStar_Option.get ftok_name_opt  in
            (fname, uu____72097, env1)
  
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
      let uu____72148 = lookup_fvar_binding env a  in
      match uu____72148 with
      | FStar_Pervasives_Native.None  ->
          let uu____72151 =
            let uu____72153 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____72153  in
          failwith uu____72151
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
              let uu___899_72200 = env  in
              let uu____72201 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___899_72200.bvar_bindings);
                fvar_bindings = uu____72201;
                depth = (uu___899_72200.depth);
                tcenv = (uu___899_72200.tcenv);
                warn = (uu___899_72200.warn);
                nolabels = (uu___899_72200.nolabels);
                use_zfuel_name = (uu___899_72200.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___899_72200.encode_non_total_function_typ);
                current_module_name = (uu___899_72200.current_module_name);
                encoding_quantifier = (uu___899_72200.encoding_quantifier);
                global_cache = (uu___899_72200.global_cache)
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
          let uu____72301 =
            let uu____72309 =
              let uu____72312 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                 in
              [uu____72312]  in
            (f, uu____72309)  in
          FStar_SMTEncoding_Util.mkApp uu____72301  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___917_72322 = env  in
        let uu____72323 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___917_72322.bvar_bindings);
          fvar_bindings = uu____72323;
          depth = (uu___917_72322.depth);
          tcenv = (uu___917_72322.tcenv);
          warn = (uu___917_72322.warn);
          nolabels = (uu___917_72322.nolabels);
          use_zfuel_name = (uu___917_72322.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___917_72322.encode_non_total_function_typ);
          current_module_name = (uu___917_72322.current_module_name);
          encoding_quantifier = (uu___917_72322.encoding_quantifier);
          global_cache = (uu___917_72322.global_cache)
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
      let uu____72361 = lookup_fvar_binding env l  in
      match uu____72361 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          if fvb.fvb_thunked
          then
            let uu____72370 = force_thunk fvb  in
            FStar_Pervasives_Native.Some uu____72370
          else
            (match fvb.smt_fuel_partial_app with
             | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                 FStar_Pervasives_Native.Some f
             | uu____72376 ->
                 (match fvb.smt_token with
                  | FStar_Pervasives_Native.Some t ->
                      (match t.FStar_SMTEncoding_Term.tm with
                       | FStar_SMTEncoding_Term.App (uu____72384,fuel::[]) ->
                           let uu____72388 =
                             let uu____72390 =
                               let uu____72392 =
                                 FStar_SMTEncoding_Term.fv_of_term fuel  in
                               FStar_All.pipe_right uu____72392
                                 FStar_SMTEncoding_Term.fv_name
                                in
                             FStar_Util.starts_with uu____72390 "fuel"  in
                           if uu____72388
                           then
                             let uu____72398 =
                               let uu____72399 =
                                 let uu____72400 =
                                   FStar_SMTEncoding_Term.mk_fv
                                     ((fvb.smt_id),
                                       FStar_SMTEncoding_Term.Term_sort)
                                    in
                                 FStar_All.pipe_left
                                   FStar_SMTEncoding_Util.mkFreeV uu____72400
                                  in
                               FStar_SMTEncoding_Term.mk_ApplyTF uu____72399
                                 fuel
                                in
                             FStar_All.pipe_left
                               (fun _72404  ->
                                  FStar_Pervasives_Native.Some _72404)
                               uu____72398
                           else FStar_Pervasives_Native.Some t
                       | uu____72407 -> FStar_Pervasives_Native.Some t)
                  | uu____72408 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____72426 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____72426 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____72430 =
            let uu____72432 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____72432  in
          failwith uu____72430
  
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
            FStar_SMTEncoding_Term.freevars = uu____72494;
            FStar_SMTEncoding_Term.rng = uu____72495;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + (Prims.parse_int "1")))
      | uu____72520 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____72536 =
                 let uu____72541 = force_thunk fvb  in
                 FStar_Util.Inr uu____72541  in
               (uu____72536, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + (Prims.parse_int "1")))
                | uu____72582 ->
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
      let uu____72605 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      FStar_Util.psmap_find_map uu____72605
        (fun uu____72625  ->
           fun fvb  ->
             check_valid_fvb fvb;
             if fvb.smt_id = nm
             then fvb.smt_token
             else FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___977_72641 = env  in
    let uu____72642 =
      let uu____72651 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____72651, [])  in
    {
      bvar_bindings = (uu___977_72641.bvar_bindings);
      fvar_bindings = uu____72642;
      depth = (uu___977_72641.depth);
      tcenv = (uu___977_72641.tcenv);
      warn = (uu___977_72641.warn);
      nolabels = (uu___977_72641.nolabels);
      use_zfuel_name = (uu___977_72641.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___977_72641.encode_non_total_function_typ);
      current_module_name = (uu___977_72641.current_module_name);
      encoding_quantifier = (uu___977_72641.encoding_quantifier);
      global_cache = (uu___977_72641.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___982_72705 = env  in
      let uu____72706 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___982_72705.bvar_bindings);
        fvar_bindings = uu____72706;
        depth = (uu___982_72705.depth);
        tcenv = (uu___982_72705.tcenv);
        warn = (uu___982_72705.warn);
        nolabels = (uu___982_72705.nolabels);
        use_zfuel_name = (uu___982_72705.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___982_72705.encode_non_total_function_typ);
        current_module_name = (uu___982_72705.current_module_name);
        encoding_quantifier = (uu___982_72705.encoding_quantifier);
        global_cache = (uu___982_72705.global_cache)
      }
  