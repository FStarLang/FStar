open Prims
exception Inner_let_rec of (Prims.string * FStar_Range.range) Prims.list 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec uu____46 -> true | uu____55 -> false
  
let (__proj__Inner_let_rec__item__uu___ :
  Prims.exn -> (Prims.string * FStar_Range.range) Prims.list) =
  fun projectee  -> match projectee with | Inner_let_rec uu____77 -> uu____77 
let add_fuel :
  'uuuuuu92 . 'uuuuuu92 -> 'uuuuuu92 Prims.list -> 'uuuuuu92 Prims.list =
  fun x  ->
    fun tl  ->
      let uu____109 = FStar_Options.unthrottle_inductives ()  in
      if uu____109 then tl else x :: tl
  
let withenv :
  'uuuuuu127 'uuuuuu128 'uuuuuu129 .
    'uuuuuu127 ->
      ('uuuuuu128 * 'uuuuuu129) -> ('uuuuuu128 * 'uuuuuu129 * 'uuuuuu127)
  = fun c  -> fun uu____149  -> match uu____149 with | (a,b) -> (a, b, c) 
let vargs :
  'uuuuuu165 'uuuuuu166 'uuuuuu167 .
    (('uuuuuu165,'uuuuuu166) FStar_Util.either * 'uuuuuu167) Prims.list ->
      (('uuuuuu165,'uuuuuu166) FStar_Util.either * 'uuuuuu167) Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___0_214  ->
         match uu___0_214 with
         | (FStar_Util.Inl uu____224,uu____225) -> false
         | uu____231 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let uu____264 =
        let uu____266 = FStar_Ident.string_of_lid lid  in
        let uu____268 = FStar_Ident.text_of_id a.FStar_Syntax_Syntax.ppname
           in
        FStar_Util.format2 "%s_%s" uu____266 uu____268  in
      FStar_All.pipe_left escape uu____264
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____298 =
          let uu____299 =
            let uu____301 = FStar_Ident.string_of_lid lid  in
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) uu____301
             in
          failwith uu____299  in
        let uu____305 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____305 with
        | (uu____311,t) ->
            let uu____313 =
              let uu____314 = FStar_Syntax_Subst.compress t  in
              uu____314.FStar_Syntax_Syntax.n  in
            (match uu____313 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____340 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____340 with
                  | (binders,uu____347) ->
                      if
                        (i < Prims.int_zero) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____374 -> fail ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____389 =
        let uu____391 = FStar_Ident.string_of_lid lid  in
        FStar_Util.format2 "%s_%s" uu____391 (Prims.string_of_int i)  in
      FStar_All.pipe_left escape uu____389
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____407 =
        let uu____408 =
          let uu____414 = mk_term_projector_name lid a  in
          (uu____414,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____408  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____407
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____430 =
        let uu____431 =
          let uu____437 = mk_term_projector_name_by_pos lid i  in
          (uu____437,
            (FStar_SMTEncoding_Term.Arrow
               (FStar_SMTEncoding_Term.Term_sort,
                 FStar_SMTEncoding_Term.Term_sort)))
           in
        FStar_SMTEncoding_Term.mk_fv uu____431  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____430
  
let mk_data_tester :
  'uuuuuu449 .
    'uuuuuu449 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  ->
        let uu____465 =
          let uu____467 = FStar_Ident.string_of_lid l  in escape uu____467
           in
        FStar_SMTEncoding_Term.mk_tester uu____465 x
  
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
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> pop
  
let (__proj__Mkvarops_t__item__snapshot :
  varops_t -> unit -> (Prims.int * unit)) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> snapshot
  
let (__proj__Mkvarops_t__item__rollback :
  varops_t -> Prims.int FStar_Pervasives_Native.option -> unit) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> rollback
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> fresh
  
let (__proj__Mkvarops_t__item__reset_fresh : varops_t -> unit -> unit) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> reset_fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> unit -> Prims.int) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push; pop; snapshot; rollback; new_var; new_fvar; fresh; reset_fresh;
        string_const; next_id; mk_unique;_} -> mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.of_int (100))  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____1571 =
    let uu____1572 = FStar_Util.smap_create (Prims.of_int (100))  in
    let uu____1578 = FStar_Util.smap_create (Prims.of_int (100))  in
    (uu____1572, uu____1578)  in
  let scopes =
    let uu____1601 = let uu____1613 = new_scope ()  in [uu____1613]  in
    FStar_Util.mk_ref uu____1601  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____1665 =
        let uu____1669 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____1669
          (fun uu____1735  ->
             match uu____1735 with
             | (names,uu____1749) -> FStar_Util.smap_try_find names y1)
         in
      match uu____1665 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____1763 ->
          (FStar_Util.incr ctr;
           (let uu____1767 =
              let uu____1769 =
                let uu____1771 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____1771  in
              Prims.op_Hat "__" uu____1769  in
            Prims.op_Hat y1 uu____1767))
       in
    let top_scope =
      let uu____1799 =
        let uu____1809 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____1809
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____1799  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    let uu____1905 =
      let uu____1907 = FStar_Ident.text_of_id pp  in
      Prims.op_Hat uu____1907 (Prims.op_Hat "__" (Prims.string_of_int rn))
       in
    FStar_All.pipe_left mk_unique uu____1905  in
  let new_fvar lid =
    let uu____1919 = FStar_Ident.string_of_lid lid  in mk_unique uu____1919
     in
  let next_id uu____1927 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh mname pfx =
    let uu____1966 =
      let uu____1968 = next_id ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1968  in
    FStar_Util.format3 "%s_%s_%s" pfx mname uu____1966  in
  let reset_fresh uu____1978 = FStar_ST.op_Colon_Equals ctr initial_ctr  in
  let string_const s =
    let uu____2008 =
      let uu____2011 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____2011
        (fun uu____2076  ->
           match uu____2076 with
           | (uu____2088,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____2008 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id ()  in
        let f =
          let uu____2104 = FStar_SMTEncoding_Util.mk_String_const id  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____2104  in
        let top_scope =
          let uu____2108 =
            let uu____2118 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____2118  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____2108  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push uu____2202 =
    let uu____2203 =
      let uu____2215 = new_scope ()  in
      let uu____2225 = FStar_ST.op_Bang scopes  in uu____2215 :: uu____2225
       in
    FStar_ST.op_Colon_Equals scopes uu____2203  in
  let pop uu____2333 =
    let uu____2334 =
      let uu____2346 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____2346
       in
    FStar_ST.op_Colon_Equals scopes uu____2334  in
  let snapshot uu____2459 = FStar_Common.snapshot push scopes ()  in
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
    string_const;
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
    let term_opt_to_string uu___1_2670 =
      match uu___1_2670 with
      | FStar_Pervasives_Native.None  -> "None"
      | FStar_Pervasives_Native.Some s ->
          FStar_SMTEncoding_Term.print_smt_term s
       in
    let uu____2676 = FStar_Ident.string_of_lid fvb.fvar_lid  in
    let uu____2678 = term_opt_to_string fvb.smt_token  in
    let uu____2680 = term_opt_to_string fvb.smt_fuel_partial_app  in
    let uu____2682 = FStar_Util.string_of_bool fvb.fvb_thunked  in
    FStar_Util.format5
      "{ lid = %s;\n  smt_id = %s;\n  smt_token = %s;\n smt_fuel_partial_app = %s;\n fvb_thunked = %s }"
      uu____2676 fvb.smt_id uu____2678 uu____2680 uu____2682
  
let (check_valid_fvb : fvar_binding -> unit) =
  fun fvb  ->
    if
      ((FStar_Option.isSome fvb.smt_token) ||
         (FStar_Option.isSome fvb.smt_fuel_partial_app))
        && fvb.fvb_thunked
    then
      (let uu____2693 =
         let uu____2695 = FStar_Ident.string_of_lid fvb.fvar_lid  in
         FStar_Util.format1 "Unexpected thunked SMT symbol: %s" uu____2695
          in
       failwith uu____2693)
    else
      if fvb.fvb_thunked && (fvb.smt_arity <> Prims.int_zero)
      then
        (let uu____2703 =
           let uu____2705 = FStar_Ident.string_of_lid fvb.fvar_lid  in
           FStar_Util.format1 "Unexpected arity of thunked SMT symbol: %s"
             uu____2705
            in
         failwith uu____2703)
      else ();
    (match fvb.smt_token with
     | FStar_Pervasives_Native.Some
         {
           FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.FreeV
             uu____2710;
           FStar_SMTEncoding_Term.freevars = uu____2711;
           FStar_SMTEncoding_Term.rng = uu____2712;_}
         ->
         let uu____2733 =
           let uu____2735 = fvb_to_string fvb  in
           FStar_Util.format1 "bad fvb\n%s" uu____2735  in
         failwith uu____2733
     | uu____2738 -> ())
  
let binder_of_eithervar :
  'uuuuuu2748 'uuuuuu2749 .
    'uuuuuu2748 -> ('uuuuuu2748 * 'uuuuuu2749 FStar_Pervasives_Native.option)
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
                    fun uu____3405  ->
                      fun acc1  ->
                        match uu____3405 with
                        | (x,_term) ->
                            let uu____3420 =
                              FStar_Syntax_Print.bv_to_string x  in
                            uu____3420 :: acc1) acc) []
       in
    let allvars =
      let uu____3427 =
        FStar_All.pipe_right e.fvar_bindings FStar_Pervasives_Native.fst  in
      FStar_Util.psmap_fold uu____3427
        (fun _k  -> fun fvb  -> fun acc  -> (fvb.fvar_lid) :: acc) []
       in
    let last_fvar =
      match FStar_List.rev allvars with
      | [] -> ""
      | l::uu____3460 ->
          let uu____3463 = FStar_Syntax_Print.lid_to_string l  in
          Prims.op_Hat "...," uu____3463
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
      let uu____3485 =
        let uu____3494 = FStar_Ident.text_of_id bv.FStar_Syntax_Syntax.ppname
           in
        FStar_Util.psmap_try_find env.bvar_bindings uu____3494  in
      match uu____3485 with
      | FStar_Pervasives_Native.Some bvs ->
          FStar_Util.pimap_try_find bvs bv.FStar_Syntax_Syntax.index
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
  
let (lookup_fvar_binding :
  env_t -> FStar_Ident.lident -> fvar_binding FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun lid  ->
      let uu____3548 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      let uu____3565 = FStar_Ident.string_of_lid lid  in
      FStar_Util.psmap_try_find uu____3548 uu____3565
  
let add_bvar_binding :
  'uuuuuu3574 .
    (FStar_Syntax_Syntax.bv * 'uuuuuu3574) ->
      (FStar_Syntax_Syntax.bv * 'uuuuuu3574) FStar_Util.pimap
        FStar_Util.psmap ->
        (FStar_Syntax_Syntax.bv * 'uuuuuu3574) FStar_Util.pimap
          FStar_Util.psmap
  =
  fun bvb  ->
    fun bvbs  ->
      let uu____3617 =
        FStar_Ident.text_of_id
          (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.ppname
         in
      FStar_Util.psmap_modify bvbs uu____3617
        (fun pimap_opt  ->
           let uu____3636 =
             let uu____3643 = FStar_Util.pimap_empty ()  in
             FStar_Util.dflt uu____3643 pimap_opt  in
           FStar_Util.pimap_add uu____3636
             (FStar_Pervasives_Native.fst bvb).FStar_Syntax_Syntax.index bvb)
  
let (add_fvar_binding :
  fvar_binding ->
    (fvar_binding FStar_Util.psmap * fvar_binding Prims.list) ->
      (fvar_binding FStar_Util.psmap * fvar_binding Prims.list))
  =
  fun fvb  ->
    fun uu____3690  ->
      match uu____3690 with
      | (fvb_map,fvb_list) ->
          let uu____3717 =
            let uu____3720 = FStar_Ident.string_of_lid fvb.fvar_lid  in
            FStar_Util.psmap_add fvb_map uu____3720 fvb  in
          (uu____3717, (fvb :: fvb_list))
  
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
        let uu____3753 =
          let uu____3754 = FStar_SMTEncoding_Term.mk_fv (xsym, s)  in
          FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3754  in
        (xsym, uu____3753)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string * FStar_SMTEncoding_Term.term * env_t))
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.op_Hat "@x" (Prims.string_of_int env.depth)  in
      let y =
        let uu____3779 =
          FStar_SMTEncoding_Term.mk_fv
            (ysym, FStar_SMTEncoding_Term.Term_sort)
           in
        FStar_All.pipe_left FStar_SMTEncoding_Util.mkFreeV uu____3779  in
      let uu____3781 =
        let uu___241_3782 = env  in
        let uu____3783 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3783;
          fvar_bindings = (uu___241_3782.fvar_bindings);
          depth = (env.depth + Prims.int_one);
          tcenv = (uu___241_3782.tcenv);
          warn = (uu___241_3782.warn);
          nolabels = (uu___241_3782.nolabels);
          use_zfuel_name = (uu___241_3782.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___241_3782.encode_non_total_function_typ);
          current_module_name = (uu___241_3782.current_module_name);
          encoding_quantifier = (uu___241_3782.encoding_quantifier);
          global_cache = (uu___241_3782.global_cache)
        }  in
      (ysym, y, uu____3781)
  
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
      let uu____3818 =
        let uu___247_3819 = env  in
        let uu____3820 = add_bvar_binding (x, y) env.bvar_bindings  in
        {
          bvar_bindings = uu____3820;
          fvar_bindings = (uu___247_3819.fvar_bindings);
          depth = (uu___247_3819.depth);
          tcenv = (uu___247_3819.tcenv);
          warn = (uu___247_3819.warn);
          nolabels = (uu___247_3819.nolabels);
          use_zfuel_name = (uu___247_3819.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___247_3819.encode_non_total_function_typ);
          current_module_name = (uu___247_3819.current_module_name);
          encoding_quantifier = (uu___247_3819.encoding_quantifier);
          global_cache = (uu___247_3819.global_cache)
        }  in
      (ysym, y, uu____3818)
  
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
        let uu____3861 =
          let uu___254_3862 = env  in
          let uu____3863 = add_bvar_binding (x, y) env.bvar_bindings  in
          {
            bvar_bindings = uu____3863;
            fvar_bindings = (uu___254_3862.fvar_bindings);
            depth = (uu___254_3862.depth);
            tcenv = (uu___254_3862.tcenv);
            warn = (uu___254_3862.warn);
            nolabels = (uu___254_3862.nolabels);
            use_zfuel_name = (uu___254_3862.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___254_3862.encode_non_total_function_typ);
            current_module_name = (uu___254_3862.current_module_name);
            encoding_quantifier = (uu___254_3862.encoding_quantifier);
            global_cache = (uu___254_3862.global_cache)
          }  in
        (ysym, y, uu____3861)
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___259_3889 = env  in
        let uu____3890 = add_bvar_binding (x, t) env.bvar_bindings  in
        {
          bvar_bindings = uu____3890;
          fvar_bindings = (uu___259_3889.fvar_bindings);
          depth = (uu___259_3889.depth);
          tcenv = (uu___259_3889.tcenv);
          warn = (uu___259_3889.warn);
          nolabels = (uu___259_3889.nolabels);
          use_zfuel_name = (uu___259_3889.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___259_3889.encode_non_total_function_typ);
          current_module_name = (uu___259_3889.current_module_name);
          encoding_quantifier = (uu___259_3889.encoding_quantifier);
          global_cache = (uu___259_3889.global_cache)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let uu____3910 = lookup_bvar_binding env a  in
      match uu____3910 with
      | FStar_Pervasives_Native.None  ->
          let uu____3921 = lookup_bvar_binding env a  in
          (match uu____3921 with
           | FStar_Pervasives_Native.None  ->
               let uu____3932 =
                 let uu____3934 = FStar_Syntax_Print.bv_to_string a  in
                 let uu____3936 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found  %s in environment: %s"
                   uu____3934 uu____3936
                  in
               failwith uu____3932
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
          let uu____4035 =
            if thunked
            then (FStar_Pervasives_Native.None, FStar_Pervasives_Native.None)
            else
              (let ftok_name = Prims.op_Hat fname "@tok"  in
               let ftok = FStar_SMTEncoding_Util.mkApp (ftok_name, [])  in
               ((FStar_Pervasives_Native.Some ftok_name),
                 (FStar_Pervasives_Native.Some ftok)))
             in
          match uu____4035 with
          | (ftok_name,ftok) ->
              let fvb =
                mk_fvb x fname arity ftok FStar_Pervasives_Native.None
                  thunked
                 in
              let uu____4099 =
                let uu___293_4100 = env  in
                let uu____4101 = add_fvar_binding fvb env.fvar_bindings  in
                {
                  bvar_bindings = (uu___293_4100.bvar_bindings);
                  fvar_bindings = uu____4101;
                  depth = (uu___293_4100.depth);
                  tcenv = (uu___293_4100.tcenv);
                  warn = (uu___293_4100.warn);
                  nolabels = (uu___293_4100.nolabels);
                  use_zfuel_name = (uu___293_4100.use_zfuel_name);
                  encode_non_total_function_typ =
                    (uu___293_4100.encode_non_total_function_typ);
                  current_module_name = (uu___293_4100.current_module_name);
                  encoding_quantifier = (uu___293_4100.encoding_quantifier);
                  global_cache = (uu___293_4100.global_cache)
                }  in
              (fname, ftok_name, uu____4099)
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident -> Prims.int -> (Prims.string * Prims.string * env_t))
  =
  fun env  ->
    fun x  ->
      fun arity  ->
        let uu____4140 =
          new_term_constant_and_tok_from_lid_aux env x arity false  in
        match uu____4140 with
        | (fname,ftok_name_opt,env1) ->
            let uu____4171 = FStar_Option.get ftok_name_opt  in
            (fname, uu____4171, env1)
  
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
      let uu____4222 = lookup_fvar_binding env a  in
      match uu____4222 with
      | FStar_Pervasives_Native.None  ->
          let uu____4225 =
            let uu____4227 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____4227  in
          failwith uu____4225
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
              let uu___319_4274 = env  in
              let uu____4275 = add_fvar_binding fvb env.fvar_bindings  in
              {
                bvar_bindings = (uu___319_4274.bvar_bindings);
                fvar_bindings = uu____4275;
                depth = (uu___319_4274.depth);
                tcenv = (uu___319_4274.tcenv);
                warn = (uu___319_4274.warn);
                nolabels = (uu___319_4274.nolabels);
                use_zfuel_name = (uu___319_4274.use_zfuel_name);
                encode_non_total_function_typ =
                  (uu___319_4274.encode_non_total_function_typ);
                current_module_name = (uu___319_4274.current_module_name);
                encoding_quantifier = (uu___319_4274.encoding_quantifier);
                global_cache = (uu___319_4274.global_cache)
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
          let uu____4375 =
            let uu____4383 =
              let uu____4386 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])  in
              [uu____4386]  in
            (f, uu____4383)  in
          FStar_SMTEncoding_Util.mkApp uu____4375  in
        let fvb1 =
          mk_fvb x fvb.smt_id fvb.smt_arity fvb.smt_token
            (FStar_Pervasives_Native.Some t3) false
           in
        let uu___337_4396 = env  in
        let uu____4397 = add_fvar_binding fvb1 env.fvar_bindings  in
        {
          bvar_bindings = (uu___337_4396.bvar_bindings);
          fvar_bindings = uu____4397;
          depth = (uu___337_4396.depth);
          tcenv = (uu___337_4396.tcenv);
          warn = (uu___337_4396.warn);
          nolabels = (uu___337_4396.nolabels);
          use_zfuel_name = (uu___337_4396.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___337_4396.encode_non_total_function_typ);
          current_module_name = (uu___337_4396.current_module_name);
          encoding_quantifier = (uu___337_4396.encoding_quantifier);
          global_cache = (uu___337_4396.global_cache)
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
      let uu____4435 = lookup_fvar_binding env l  in
      match uu____4435 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some fvb ->
          ((let uu____4442 =
              FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
                (FStar_Options.Other "PartialApp")
               in
            if uu____4442
            then
              let uu____4447 = FStar_Ident.string_of_lid l  in
              let uu____4449 = fvb_to_string fvb  in
              FStar_Util.print2 "Looked up %s found\n%s\n" uu____4447
                uu____4449
            else ());
           if fvb.fvb_thunked
           then
             (let uu____4457 = force_thunk fvb  in
              FStar_Pervasives_Native.Some uu____4457)
           else
             (match fvb.smt_fuel_partial_app with
              | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
                  FStar_Pervasives_Native.Some f
              | uu____4463 ->
                  (match fvb.smt_token with
                   | FStar_Pervasives_Native.Some t ->
                       (match t.FStar_SMTEncoding_Term.tm with
                        | FStar_SMTEncoding_Term.App (uu____4471,fuel::[]) ->
                            let uu____4475 =
                              let uu____4477 =
                                let uu____4479 =
                                  FStar_SMTEncoding_Term.fv_of_term fuel  in
                                FStar_All.pipe_right uu____4479
                                  FStar_SMTEncoding_Term.fv_name
                                 in
                              FStar_Util.starts_with uu____4477 "fuel"  in
                            if uu____4475
                            then
                              let uu____4485 =
                                let uu____4486 =
                                  let uu____4487 =
                                    FStar_SMTEncoding_Term.mk_fv
                                      ((fvb.smt_id),
                                        FStar_SMTEncoding_Term.Term_sort)
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Util.mkFreeV uu____4487
                                   in
                                FStar_SMTEncoding_Term.mk_ApplyTF uu____4486
                                  fuel
                                 in
                              FStar_All.pipe_left
                                (fun uu____4491  ->
                                   FStar_Pervasives_Native.Some uu____4491)
                                uu____4485
                            else FStar_Pervasives_Native.Some t
                        | uu____4494 -> FStar_Pervasives_Native.Some t)
                   | uu____4495 -> FStar_Pervasives_Native.None)))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lid FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____4513 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____4513 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____4517 =
            let uu____4519 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____4519  in
          failwith uu____4517
  
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
            FStar_SMTEncoding_Term.freevars = uu____4581;
            FStar_SMTEncoding_Term.rng = uu____4582;_}
          when env.use_zfuel_name ->
          ((FStar_Util.Inl g), zf, (fvb.smt_arity + Prims.int_one))
      | uu____4607 ->
          (match fvb.smt_token with
           | FStar_Pervasives_Native.None  when fvb.fvb_thunked ->
               let uu____4623 =
                 let uu____4628 = force_thunk fvb  in
                 FStar_Util.Inr uu____4628  in
               (uu____4623, [], (fvb.smt_arity))
           | FStar_Pervasives_Native.None  ->
               ((FStar_Util.Inl (FStar_SMTEncoding_Term.Var (fvb.smt_id))),
                 [], (fvb.smt_arity))
           | FStar_Pervasives_Native.Some sym ->
               (match sym.FStar_SMTEncoding_Term.tm with
                | FStar_SMTEncoding_Term.App (g,fuel::[]) ->
                    ((FStar_Util.Inl g), [fuel],
                      (fvb.smt_arity + Prims.int_one))
                | uu____4669 ->
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
      let uu____4692 =
        let uu____4695 =
          FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
           in
        FStar_Util.psmap_find_map uu____4695
          (fun uu____4715  ->
             fun fvb  ->
               check_valid_fvb fvb;
               if fvb.smt_id = nm
               then fvb.smt_token
               else FStar_Pervasives_Native.None)
         in
      match uu____4692 with
      | FStar_Pervasives_Native.Some b -> FStar_Pervasives_Native.Some b
      | FStar_Pervasives_Native.None  ->
          FStar_Util.psmap_find_map env.bvar_bindings
            (fun uu____4736  ->
               fun pi  ->
                 FStar_Util.pimap_fold pi
                   (fun uu____4756  ->
                      fun y  ->
                        fun res  ->
                          match (res, y) with
                          | (FStar_Pervasives_Native.Some
                             uu____4774,uu____4775) -> res
                          | (FStar_Pervasives_Native.None
                             ,(uu____4786,{
                                            FStar_SMTEncoding_Term.tm =
                                              FStar_SMTEncoding_Term.App
                                              (FStar_SMTEncoding_Term.Var
                                               sym,[]);
                                            FStar_SMTEncoding_Term.freevars =
                                              uu____4788;
                                            FStar_SMTEncoding_Term.rng =
                                              uu____4789;_}))
                              when sym = nm ->
                              FStar_Pervasives_Native.Some
                                (FStar_Pervasives_Native.snd y)
                          | uu____4812 -> FStar_Pervasives_Native.None)
                   FStar_Pervasives_Native.None)
  
let (reset_current_module_fvbs : env_t -> env_t) =
  fun env  ->
    let uu___424_4829 = env  in
    let uu____4830 =
      let uu____4839 =
        FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.fst
         in
      (uu____4839, [])  in
    {
      bvar_bindings = (uu___424_4829.bvar_bindings);
      fvar_bindings = uu____4830;
      depth = (uu___424_4829.depth);
      tcenv = (uu___424_4829.tcenv);
      warn = (uu___424_4829.warn);
      nolabels = (uu___424_4829.nolabels);
      use_zfuel_name = (uu___424_4829.use_zfuel_name);
      encode_non_total_function_typ =
        (uu___424_4829.encode_non_total_function_typ);
      current_module_name = (uu___424_4829.current_module_name);
      encoding_quantifier = (uu___424_4829.encoding_quantifier);
      global_cache = (uu___424_4829.global_cache)
    }
  
let (get_current_module_fvbs : env_t -> fvar_binding Prims.list) =
  fun env  ->
    FStar_All.pipe_right env.fvar_bindings FStar_Pervasives_Native.snd
  
let (add_fvar_binding_to_env : fvar_binding -> env_t -> env_t) =
  fun fvb  ->
    fun env  ->
      let uu___429_4893 = env  in
      let uu____4894 = add_fvar_binding fvb env.fvar_bindings  in
      {
        bvar_bindings = (uu___429_4893.bvar_bindings);
        fvar_bindings = uu____4894;
        depth = (uu___429_4893.depth);
        tcenv = (uu___429_4893.tcenv);
        warn = (uu___429_4893.warn);
        nolabels = (uu___429_4893.nolabels);
        use_zfuel_name = (uu___429_4893.use_zfuel_name);
        encode_non_total_function_typ =
          (uu___429_4893.encode_non_total_function_typ);
        current_module_name = (uu___429_4893.current_module_name);
        encoding_quantifier = (uu___429_4893.encoding_quantifier);
        global_cache = (uu___429_4893.global_cache)
      }
  