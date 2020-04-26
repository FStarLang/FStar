open Prims
exception Inner_let_rec of (Prims.string * FStar_Range.range) Prims.list 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec uu____45 -> true | uu____54 -> false
  
let (__proj__Inner_let_rec__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) Prims.list) =
  fun projectee  -> match projectee with | Inner_let_rec uu____76 -> uu____76 
let add_fuel :
  'uuuuuu91 . 'uuuuuu91 -> 'uuuuuu91 Prims.list -> 'uuuuuu91 Prims.list =
  fun x  ->
    fun tl  ->
      let uu____108 = FStar_Options.unthrottle_inductives ()  in
      if uu____108 then tl else x :: tl
  
let withenv :
  'uuuuuu126 'uuuuuu127 'uuuuuu128 .
    'uuuuuu126 ->
      ('uuuuuu127 * 'uuuuuu128) -> ('uuuuuu127 * 'uuuuuu128 * 'uuuuuu126)
  = fun c  -> fun uu____148  -> match uu____148 with | (a,b) -> (a, b, c) 
let vargs :
  'uuuuuu164 'uuuuuu165 'uuuuuu166 .
    (('uuuuuu164,'uuuuuu165) FStar_Util.either * 'uuuuuu166) Prims.list ->
      (('uuuuuu164,'uuuuuu165) FStar_Util.either * 'uuuuuu166) Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___0_213  ->
         match uu___0_213 with
         | (FStar_Util.Inl uu____223,uu____224) -> false
         | uu____230 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____263 =
        let uu____265 = FStar_Ident.string_of_lid lid  in
        let uu____267 = FStar_Ident.text_of_id a.FStar_Syntax_Syntax.ppname
           in
        FStar_Util.format2 "%s_%s" uu____265 uu____267  in
      FStar_All.pipe_left escape uu____263
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____297 =
          let uu____298 =
            let uu____300 = FStar_Ident.string_of_lid lid  in
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) uu____300
             in
          failwith uu____298  in
        let t = FStar_TypeChecker_Env.lookup_datacon_noinst env lid  in
        let uu____305 =
          let uu____306 = FStar_Syntax_Subst.compress t  in
          uu____306.FStar_Syntax_Syntax.n  in
        match uu____305 with
        | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
            let uu____332 = FStar_Syntax_Subst.open_comp bs c  in
            (match uu____332 with
             | (binders,uu____339) ->
                 if
                   (i < Prims.int_zero) || (i >= (FStar_List.length binders))
                 then fail ()
                 else
                   (let b = FStar_List.nth binders i  in
                    mk_term_projector_name lid
                      (FStar_Pervasives_Native.fst b)))
        | uu____366 -> fail ()
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____381 =
        let uu____383 = FStar_Ident.string_of_lid lid  in
        FStar_Util.format2 "%s_%s" uu____383 (Prims.string_of_int i)  in
      FStar_All.pipe_left escape uu____381
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____399 =
        let uu____400 =
          let uu____406 = mk_term_projector_name lid a  in
          (uu____406,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____400  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____399
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____422 =
        let uu____423 =
          let uu____429 = mk_term_projector_name_by_pos lid i  in
          (uu____429,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____423  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____422
  
let mk_data_tester :
  'uuuuuu441 .
    'uuuuuu441 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  ->
        let uu____457 =
          let uu____459 = FStar_Ident.string_of_lid l  in escape uu____459
           in
        FStar_SMTEncoding_Term.mk_tester uu____457 x
  
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
  next_id: unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }
let (__proj__Mkvarops_t__item__push : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> pop
  
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int * unit)) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> snapshot
  
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> rollback
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> fresh
  
let (__proj__Mkvarops_t__item__reset_fresh : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> reset_fresh
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        next_id; mk_unique;_} -> mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.of_int (100))  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____1413 = FStar_Util.smap_create (Prims.of_int (100))  in
  let scopes =
    let uu____1427 = let uu____1433 = new_scope ()  in [uu____1433]  in
    FStar_Util.mk_ref uu____1427  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1461 =
        let uu____1465 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1465
          (fun names  -> FStar_Util.smap_try_find names y1)
         in
      match uu____1461 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1512 ->
          (FStar_Util.incr ctr;
           (let uu____1516 =
              let uu____1518 =
                let uu____1520 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1520  in
              Prims.op_Hat "__" uu____1518  in
            Prims.op_Hat y1 uu____1516))
       in
    let top_scope =
      let uu____1548 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1548
       in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    let uu____1603 =
      let uu____1605 = FStar_Ident.text_of_id pp  in
      Prims.op_Hat uu____1605 (Prims.op_Hat "__" (Prims.string_of_int rn))
       in
    FStar_All.pipe_left mk_unique uu____1603  in
  let new_fvar lid =
    let uu____1617 = FStar_Ident.string_of_lid lid  in mk_unique uu____1617
     in
  let next_id uu____1625 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh mname pfx =
    let uu____1664 =
      let uu____1666 = next_id ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1666  in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____1664  in
  let reset_fresh uu____1676 = FStar_ST.op_Colon_Equals ctr initial_ctr  in
  let push uu____1703 =
    let uu____1704 =
      let uu____1710 = new_scope ()  in
      let uu____1714 = FStar_ST.op_Bang scopes  in uu____1710 :: uu____1714
       in
    FStar_ST.op_Colon_Equals scopes uu____1704  in
  let pop uu____1786 =
    let uu____1787 =
      let uu____1793 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1793
       in
    FStar_ST.op_Colon_Equals scopes uu____1787  in
  let snapshot uu____1870 = FStar_Common.snapshot push scopes ()  in
  let rollback depth = FStar_Common.rollback pop scopes depth  in
  {
    push;
    pop;
    snapshot;
    rollback;
    new_var;
    new_fvar;
    fresh;
    reset_fresh;
    next_id;
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
    let term_opt_to_string uu___1_2069 =
      match uu___1_2069 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some s ->
          FStar_SMTEncoding_Term.print_smt_term s
       in
    let uu____2075 = FStar_Ident.string_of_lid fvb.fvar_lid  in
    let uu____2077 = term_opt_to_string fvb.smt_token  in
    let uu____2079 = term_opt_to_string fvb.smt_fuel_partial_app  in
    let uu____2081 = FStar_Util.string_of_bool fvb.fvb_thunked  in
    FStar_Util.format5
      "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }"
      uu____2075 fvb.smt_id uu____2077 uu____2079 uu____2081
  
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb  ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      (let uu____2092 =
         let uu____2094 = FStar_Ident.string_of_lid fvb.fvar_lid  in
         FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2094
          in
       failwith uu____2092)
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> Prims.int_zero)
      then
        (let uu____2102 =
           let uu____2104 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____2104
            in
         failwith uu____2102)
      else ();
    (match fvb.smt_token with
     | FStar_Pervasives_Native.Some
         {
           FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
             uu____2109;
           FStar_SMTEncoding_Term.freevars = uu____2110;
           FStar_SMTEncoding_Term.rng = uu____2111;_}
         ->
         let uu____2132 =
           let uu____2134 = fvb_to_string fvb  in
           FStar_Util.format1 "bad fvb\n%s" uu____2134  in
         failwith uu____2132
     | uu____2137 -> ())
  
let binder_of_eithervar :
  'uuuuuu2147 'uuuuuu2148 .
    'uuuuuu2147 -> ('uuuuuu2147 * 'uuuuuu2148 FStar_Pervasives_Native.option)
  = fun v  -> (v, FStar_Pervasives_Native.None) 
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
                    fun uu____2804  ->
                      fun acc1  ->
                        match uu____2804 with
                        | (x,_term) ->
                            let uu____2819 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____2819 :: acc1) acc) []
       in
    let allvars =
      let uu____2826 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____2826
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____2859 ->
          let uu____2862 = FStar_Syntax_Print.lid_to_string l  in
          Prims.op_Hat "...," uu____2862
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
      let uu____2884 =
        let uu____2893 = FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname
           in
        FStar_Util.psmap_try_find env.bvar_bindings uu____2893  in
      match uu____2884 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____2947 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      let uu____2964 = FStar_Ident.string_of_lid lid  in
      FStar_Util.psmap_try_find uu____2947 uu____2964
  
let add_bvar_binding :
  'uuuuuu2973 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu2973) ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu2973) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu2973) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      let uu____3016 =
        FStar_Ident.text_of_id
          (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname
         in
      FStar_Util.psmap_modify bvbs uu____3016
        (fun pimap_opt  ->
           let uu____3035 =
             let uu____3042 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3042 pimap_opt  in
           FStar_Util.pimap_add uu____3035
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3089  ->
      match uu____3089 with
      | (fvb_map,fvb_list) ->
          let uu____3116 =
            let uu____3119 = FStar_Ident.string_of_lid fvb.fvar_lid  in
            FStar_Util.psmap_add fvb_map uu____3119 fvb  in
          (uu____3116, (fvb :: fvb_list))
  
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
        let uu____3152 =
          let uu____3153 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3153  in
        (xsym, uu____3152)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____3178 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3178  in
      let uu____3180 =
        let uu___222_3181 = env  in
        let uu____3182 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3182;
          fvar_bindings = (uu___222_3181.fvar_bindings);
          depth = (env.depth + Prims.int_one);
          tcenv = (uu___222_3181.tcenv);
          warn = (uu___222_3181.warn);
          nolabels = (uu___222_3181.nolabels);
          use_zfuel_name = (uu___222_3181.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___222_3181.encode_non_total_function_typ);
          current_module_name = (uu___222_3181.current_module_name);
          encoding_quantifier = (uu___222_3181.encoding_quantifier);
          global_cache = (uu___222_3181.global_cache)
        }  in
      (ysym, y, uu____3180)
  
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
      let uu____3217 =
        let uu___228_3218 = env  in
        let uu____3219 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3219;
          fvar_bindings = (uu___228_3218.fvar_bindings);
          depth = (uu___228_3218.depth);
          tcenv = (uu___228_3218.tcenv);
          warn = (uu___228_3218.warn);
          nolabels = (uu___228_3218.nolabels);
          use_zfuel_name = (uu___228_3218.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___228_3218.encode_non_total_function_typ);
          current_module_name = (uu___228_3218.current_module_name);
          encoding_quantifier = (uu___228_3218.encoding_quantifier);
          global_cache = (uu___228_3218.global_cache)
        }  in
      (ysym, y, uu____3217)
  
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
        let uu____3260 =
          let uu___235_3261 = env  in
          let uu____3262 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3262;
            fvar_bindings = (uu___235_3261.fvar_bindings);
            depth = (uu___235_3261.depth);
            tcenv = (uu___235_3261.tcenv);
            warn = (uu___235_3261.warn);
            nolabels = (uu___235_3261.nolabels);
            use_zfuel_name = (uu___235_3261.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___235_3261.encode_non_total_function_typ);
            current_module_name = (uu___235_3261.current_module_name);
            encoding_quantifier = (uu___235_3261.encoding_quantifier);
            global_cache = (uu___235_3261.global_cache)
          }  in
        (ysym, y, uu____3260)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___240_3288 = env  in
        let uu____3289 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3289;
          fvar_bindings = (uu___240_3288.fvar_bindings);
          depth = (uu___240_3288.depth);
          tcenv = (uu___240_3288.tcenv);
          warn = (uu___240_3288.warn);
          nolabels = (uu___240_3288.nolabels);
          use_zfuel_name = (uu___240_3288.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___240_3288.encode_non_total_function_typ);
          current_module_name = (uu___240_3288.current_module_name);
          encoding_quantifier = (uu___240_3288.encoding_quantifier);
          global_cache = (uu___240_3288.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3309 = lookup_bvar_binding env a  in
      match uu____3309 with
      | FStar_Pervasives_Native.None  ->
          let uu____3320 = lookup_bvar_binding env a  in
          (match uu____3320 with
           | FStar_Pervasives_Native.None  ->
               let uu____3331 =
                 let uu____3333 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3335 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3333 uu____3335
                  in
               failwith uu____3331
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
          let uu____3434 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____3434 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____3498 =
                let uu___274_3499 = env  in
                let uu____3500 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___274_3499.bvar_bindings);
                  fvar_bindings = uu____3500;
                  depth = (uu___274_3499.depth);
                  tcenv = (uu___274_3499.tcenv);
                  warn = (uu___274_3499.warn);
                  nolabels = (uu___274_3499.nolabels);
                  use_zfuel_name = (uu___274_3499.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___274_3499.encode_non_total_function_typ);
                  current_module_name = (uu___274_3499.current_module_name);
                  encoding_quantifier = (uu___274_3499.encoding_quantifier);
                  global_cache = (uu___274_3499.global_cache)
                }  in
              (fname, ftok_name, uu____3498)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____3539 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____3539 with
        | (fname,ftok_name_opt,env1) ->
            let uu____3570 = FStar_Option.get ftok_name_opt  in
            (fname, uu____3570, env1)
  
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
      let uu____3621 = lookup_fvar_binding env a  in
      match uu____3621 with
      | FStar_Pervasives_Native.None  ->
          let uu____3624 =
            let uu____3626 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____3626  in
          failwith uu____3624
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
              let uu___300_3673 = env  in
              let uu____3674 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___300_3673.bvar_bindings);
                fvar_bindings = uu____3674;
                depth = (uu___300_3673.depth);
                tcenv = (uu___300_3673.tcenv);
                warn = (uu___300_3673.warn);
                nolabels = (uu___300_3673.nolabels);
                use_zfuel_name = (uu___300_3673.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___300_3673.encode_non_total_function_typ);
                current_module_name = (uu___300_3673.current_module_name);
                encoding_quantifier = (uu___300_3673.encoding_quantifier);
                global_cache = (uu___300_3673.global_cache)
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
              (arity = Prims.int_zero)
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let fvb = lookup_lid env x  in
        let t3 =
          let uu____3774 =
            let uu____3782 =
              let uu____3785 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____3785]  in
            (f, uu____3782)  in
          FStar_SMTEncoding_Util.mkApp uu____3774  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___318_3795 = env  in
        let uu____3796 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___318_3795.bvar_bindings);
          fvar_bindings = uu____3796;
          depth = (uu___318_3795.depth);
          tcenv = (uu___318_3795.tcenv);
          warn = (uu___318_3795.warn);
          nolabels = (uu___318_3795.nolabels);
          use_zfuel_name = (uu___318_3795.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___318_3795.encode_non_total_function_typ);
          current_module_name = (uu___318_3795.current_module_name);
          encoding_quantifier = (uu___318_3795.encoding_quantifier);
          global_cache = (uu___318_3795.global_cache)
        }
  
let (force_thunk : fvar_binding -> FStar_SMTEncoding_Term.term) =
  fun fvb  ->
    if
      (Prims.op_Negation fvb.fvb_thunked) ||
        (fvb.smt_arity <> Prims.int_zero)
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
      let uu____3834 = lookup_fvar_binding env l  in
      match uu____3834 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          ((let uu____3841 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
                (FStar_Options.Other "PartialApp")
               in
            if uu____3841
            then
              let uu____3846 = FStar_Ident.string_of_lid l  in
              let uu____3848 = fvb_to_string fvb  in
              FStar_Util.print2 "Looked up %s found\n%s\n" uu____3846
                uu____3848
            else ());
           if fvb.fvb_thunked
           then
             (let uu____3856 = force_thunk fvb  in
              FStar_Pervasives_Native.Some uu____3856)
           else
             (match fvb.smt_fuel_partial_app with
              | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                  FStar_Pervasives_Native.Some f
              | uu____3862 ->
                  (match fvb.smt_token with
                   | FStar_Pervasives_Native.Some t ->
                       (match t.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App (uu____3870,fuel::[]) ->
                            let uu____3874 =
                              let uu____3876 =
                                let uu____3878 =
                                  FStar_SMTEncoding_Term.fv_of_term fuel  in
                                FStar_All.pipe_right uu____3878
                                  FStar_SMTEncoding_Term.fv_name
                                 in
                              FStar_Util.starts_with uu____3876 "fuel"  in
                            if uu____3874
                            then
                              let uu____3884 =
                                let uu____3885 =
                                  let uu____3886 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ((fvb.smt_id),
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Util.mkFreeV uu____3886
                                   in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu____3885
                                  fuel
                                 in
                              FStar_All.pipe_left
                                (fun uu____3890  ->
                                   FStar_Pervasives_Native.Some uu____3890)
                                uu____3884
                            else FStar_Pervasives_Native.Some t
                        | uu____3893 -> FStar_Pervasives_Native.Some t)
                   | uu____3894 -> FStar_Pervasives_Native.None)))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____3912 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____3912 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____3916 =
            let uu____3918 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____3918  in
          failwith uu____3916
  
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
            FStar_SMTEncoding_Term.freevars = uu____3980;
            FStar_SMTEncoding_Term.rng = uu____3981;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + Prims.int_one))
      | uu____4006 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____4022 =
                 let uu____4027 = force_thunk fvb  in
                 FStar_Util.Inr uu____4027  in
               (uu____4022, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + Prims.int_one))
                | uu____4068 ->
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
      let uu____4091 =
        let uu____4094 =
          FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
           in
        FStar_Util.psmap_find_map uu____4094
          (fun uu____4114  ->
             fun fvb  ->
               check_valid_fvb fvb;
               if fvb.smt_id = nm
               then fvb.smt_token
               else FStar_Pervasives_Native.None)
         in
      match uu____4091 with
      | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
      | FStar_Pervasives_Native.None  ->
          FStar_Util.psmap_find_map env.bvar_bindings
            (fun uu____4135  ->
               fun pi  ->
                 FStar_Util.pimap_fold pi
                   (fun uu____4155  ->
                      fun y  ->
                        fun res  ->
                          match (res, y) with
                          | (FStar_Pervasives_Native.Some
                             uu____4173,uu____4174) -> res
                          | (FStar_Pervasives_Native.None
                             ,(uu____4185,{
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Var
                                               sym,[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____4187;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____4188;_}))
                              when sym = nm ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.snd y)
                          | uu____4211 -> FStar_Pervasives_Native.None)
                   FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___405_4228 = env  in
    let uu____4229 =
      let uu____4238 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____4238, [])  in
    {
      bvar_bindings = (uu___405_4228.bvar_bindings);
      fvar_bindings = uu____4229;
      depth = (uu___405_4228.depth);
      tcenv = (uu___405_4228.tcenv);
      warn = (uu___405_4228.warn);
      nolabels = (uu___405_4228.nolabels);
      use_zfuel_name = (uu___405_4228.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___405_4228.encode_non_total_function_typ);
      current_module_name = (uu___405_4228.current_module_name);
      encoding_quantifier = (uu___405_4228.encoding_quantifier);
      global_cache = (uu___405_4228.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___410_4292 = env  in
      let uu____4293 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___410_4292.bvar_bindings);
        fvar_bindings = uu____4293;
        depth = (uu___410_4292.depth);
        tcenv = (uu___410_4292.tcenv);
        warn = (uu___410_4292.warn);
        nolabels = (uu___410_4292.nolabels);
        use_zfuel_name = (uu___410_4292.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___410_4292.encode_non_total_function_typ);
        current_module_name = (uu___410_4292.current_module_name);
        encoding_quantifier = (uu___410_4292.encoding_quantifier);
        global_cache = (uu___410_4292.global_cache)
      }
  