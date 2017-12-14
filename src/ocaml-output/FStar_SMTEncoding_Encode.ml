open Prims
let add_fuel :
  'Auu____4 . 'Auu____4 -> 'Auu____4 Prims.list -> 'Auu____4 Prims.list =
  fun x  ->
    fun tl1  ->
      let uu____19 = FStar_Options.unthrottle_inductives ()  in
      if uu____19 then tl1 else x :: tl1
  
let withenv :
  'Auu____28 'Auu____29 'Auu____30 .
    'Auu____30 ->
      ('Auu____29,'Auu____28) FStar_Pervasives_Native.tuple2 ->
        ('Auu____29,'Auu____28,'Auu____30) FStar_Pervasives_Native.tuple3
  = fun c  -> fun uu____48  -> match uu____48 with | (a,b) -> (a, b, c) 
let vargs :
  'Auu____59 'Auu____60 'Auu____61 .
    (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
      FStar_Pervasives_Native.tuple2 Prims.list ->
      (('Auu____61,'Auu____60) FStar_Util.either,'Auu____59)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun args  ->
    FStar_List.filter
      (fun uu___310_107  ->
         match uu___310_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
  
let subst_lcomp_opt :
  'Auu____134 .
    FStar_Syntax_Syntax.subst_elt Prims.list ->
      (FStar_Syntax_Syntax.lcomp,'Auu____134) FStar_Util.either
        FStar_Pervasives_Native.option ->
        (FStar_Syntax_Syntax.lcomp,'Auu____134) FStar_Util.either
          FStar_Pervasives_Native.option
  =
  fun s  ->
    fun l  ->
      match l with
      | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
          let uu____170 =
            let uu____175 =
              let uu____176 =
                let uu____179 = l1.FStar_Syntax_Syntax.comp ()  in
                FStar_Syntax_Subst.subst_comp s uu____179  in
              FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____176
               in
            FStar_Util.Inl uu____175  in
          FStar_Pervasives_Native.Some uu____170
      | uu____186 -> l
  
let escape : Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s 39 95 
let mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___333_205 = a  in
        let uu____206 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____206;
          FStar_Syntax_Syntax.index =
            (uu___333_205.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___333_205.FStar_Syntax_Syntax.sort)
        }  in
      let uu____207 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____207
  
let primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____220 =
          let uu____221 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____221  in
        let uu____222 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____222 with
        | (uu____227,t) ->
            let uu____229 =
              let uu____230 = FStar_Syntax_Subst.compress t  in
              uu____230.FStar_Syntax_Syntax.n  in
            (match uu____229 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____251 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____251 with
                  | (binders,uu____257) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____272 -> fail ())
  
let mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____279 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____279
  
let mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____286 =
        let uu____291 = mk_term_projector_name lid a  in
        (uu____291,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____286
  
let mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____298 =
        let uu____303 = mk_term_projector_name_by_pos lid i  in
        (uu____303,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____298
  
let mk_data_tester :
  'Auu____308 .
    'Auu____308 ->
      FStar_Ident.lident ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun l  ->
      fun x  -> FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
  
type varops_t =
  {
  push: Prims.unit -> Prims.unit ;
  pop: Prims.unit -> Prims.unit ;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string ;
  new_fvar: FStar_Ident.lident -> Prims.string ;
  fresh: Prims.string -> Prims.string ;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term ;
  next_id: Prims.unit -> Prims.int ;
  mk_unique: Prims.string -> Prims.string }[@@deriving show]
let __proj__Mkvarops_t__item__push : varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
  
let __proj__Mkvarops_t__item__pop : varops_t -> Prims.unit -> Prims.unit =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
  
let __proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
  
let __proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
  
let __proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
  
let __proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
  
let __proj__Mkvarops_t__item__next_id : varops_t -> Prims.unit -> Prims.int =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
  
let __proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
  
let varops : varops_t =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____672 =
    let uu____673 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____676 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____673, uu____676)  in
  let scopes =
    let uu____696 = let uu____707 = new_scope ()  in [uu____707]  in
    FStar_Util.mk_ref uu____696  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____748 =
        let uu____751 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____751
          (fun uu____855  ->
             match uu____855 with
             | (names1,uu____867) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____748 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____876 ->
          (FStar_Util.incr ctr;
           (let uu____899 =
              let uu____900 =
                let uu____901 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____901  in
              Prims.strcat "__" uu____900  in
            Prims.strcat y1 uu____899))
       in
    let top_scope =
      let uu____967 =
        let uu____976 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____976
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____967  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____1106 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1195 =
      let uu____1196 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1196  in
    FStar_Util.format2 "%s_%s" pfx uu____1195  in
  let string_const s =
    let uu____1201 =
      let uu____1204 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1204
        (fun uu____1308  ->
           match uu____1308 with
           | (uu____1319,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1201 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1332 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1332  in
        let top_scope =
          let uu____1336 =
            let uu____1345 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1345  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1336  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1464 =
    let uu____1465 =
      let uu____1476 = new_scope ()  in
      let uu____1485 = FStar_ST.op_Bang scopes  in uu____1476 :: uu____1485
       in
    FStar_ST.op_Colon_Equals scopes uu____1465  in
  let pop1 uu____1671 =
    let uu____1672 =
      let uu____1683 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1683
       in
    FStar_ST.op_Colon_Equals scopes uu____1672  in
  {
    push = push1;
    pop = pop1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  } 
let unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___334_1869 = x  in
    let uu____1870 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1870;
      FStar_Syntax_Syntax.index = (uu___334_1869.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___334_1869.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2 
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4 [@@deriving show]
let uu___is_Binding_var : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1903 -> false
  
let __proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let uu___is_Binding_fvar : binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1939 -> false
  
let __proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____1986 'Auu____1987 .
    'Auu____1987 ->
      ('Auu____1987,'Auu____1986 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }[@@deriving show]
let __proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let __proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let __proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let __proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_assumption_names
  
type env_t =
  {
  bindings: binding Prims.list ;
  depth: Prims.int ;
  tcenv: FStar_TypeChecker_Env.env ;
  warn: Prims.bool ;
  cache: cache_entry FStar_Util.smap ;
  nolabels: Prims.bool ;
  use_zfuel_name: Prims.bool ;
  encode_non_total_function_typ: Prims.bool ;
  current_module_name: Prims.string }[@@deriving show]
let __proj__Mkenv_t__item__bindings : env_t -> binding Prims.list =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__bindings
  
let __proj__Mkenv_t__item__depth : env_t -> Prims.int =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__depth
  
let __proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__tcenv
  
let __proj__Mkenv_t__item__warn : env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__warn
  
let __proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__cache
  
let __proj__Mkenv_t__item__nolabels : env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__nolabels
  
let __proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__use_zfuel_name
  
let __proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__encode_non_total_function_typ
  
let __proj__Mkenv_t__item__current_module_name : env_t -> Prims.string =
  fun projectee  ->
    match projectee with
    | { bindings = __fname__bindings; depth = __fname__depth;
        tcenv = __fname__tcenv; warn = __fname__warn; cache = __fname__cache;
        nolabels = __fname__nolabels;
        use_zfuel_name = __fname__use_zfuel_name;
        encode_non_total_function_typ =
          __fname__encode_non_total_function_typ;
        current_module_name = __fname__current_module_name;_} ->
        __fname__current_module_name
  
let mk_cache_entry :
  'Auu____2283 .
    'Auu____2283 ->
      Prims.string ->
        FStar_SMTEncoding_Term.sort Prims.list ->
          FStar_SMTEncoding_Term.decl Prims.list -> cache_entry
  =
  fun env  ->
    fun tsym  ->
      fun cvar_sorts  ->
        fun t_decls  ->
          let names1 =
            FStar_All.pipe_right t_decls
              (FStar_List.collect
                 (fun uu___311_2317  ->
                    match uu___311_2317 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2321 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
            cache_symbol_assumption_names = names1
          }
  
let use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let print_env : env_t -> Prims.string =
  fun e  ->
    let uu____2330 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___312_2340  ->
              match uu___312_2340 with
              | Binding_var (x,uu____2342) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2344,uu____2345,uu____2346) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____2330 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2360 .
    env_t ->
      (binding -> 'Auu____2360 FStar_Pervasives_Native.option) ->
        'Auu____2360 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____2388 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2388
      then
        let uu____2391 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2391
      else FStar_Pervasives_Native.None
  
let fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____2404 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2404)
  
let gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___335_2420 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___335_2420.tcenv);
           warn = (uu___335_2420.warn);
           cache = (uu___335_2420.cache);
           nolabels = (uu___335_2420.nolabels);
           use_zfuel_name = (uu___335_2420.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___335_2420.encode_non_total_function_typ);
           current_module_name = (uu___335_2420.current_module_name)
         }))
  
let new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      (ysym, y,
        (let uu___336_2438 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___336_2438.depth);
           tcenv = (uu___336_2438.tcenv);
           warn = (uu___336_2438.warn);
           cache = (uu___336_2438.cache);
           nolabels = (uu___336_2438.nolabels);
           use_zfuel_name = (uu___336_2438.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___336_2438.encode_non_total_function_typ);
           current_module_name = (uu___336_2438.current_module_name)
         }))
  
let new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        (ysym, y,
          (let uu___337_2459 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___337_2459.depth);
             tcenv = (uu___337_2459.tcenv);
             warn = (uu___337_2459.warn);
             cache = (uu___337_2459.cache);
             nolabels = (uu___337_2459.nolabels);
             use_zfuel_name = (uu___337_2459.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___337_2459.encode_non_total_function_typ);
             current_module_name = (uu___337_2459.current_module_name)
           }))
  
let push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___338_2469 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___338_2469.depth);
          tcenv = (uu___338_2469.tcenv);
          warn = (uu___338_2469.warn);
          cache = (uu___338_2469.cache);
          nolabels = (uu___338_2469.nolabels);
          use_zfuel_name = (uu___338_2469.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___338_2469.encode_non_total_function_typ);
          current_module_name = (uu___338_2469.current_module_name)
        }
  
let lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___313_2493  ->
             match uu___313_2493 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2506 -> FStar_Pervasives_Native.None)
         in
      let uu____2511 = aux a  in
      match uu____2511 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2523 = aux a2  in
          (match uu____2523 with
           | FStar_Pervasives_Native.None  ->
               let uu____2534 =
                 let uu____2535 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2536 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2535 uu____2536
                  in
               failwith uu____2534
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____2563 =
        let uu___339_2564 = env  in
        let uu____2565 =
          let uu____2568 =
            let uu____2569 =
              let uu____2582 =
                let uu____2585 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2585
                 in
              (x, fname, uu____2582, FStar_Pervasives_Native.None)  in
            Binding_fvar uu____2569  in
          uu____2568 :: (env.bindings)  in
        {
          bindings = uu____2565;
          depth = (uu___339_2564.depth);
          tcenv = (uu___339_2564.tcenv);
          warn = (uu___339_2564.warn);
          cache = (uu___339_2564.cache);
          nolabels = (uu___339_2564.nolabels);
          use_zfuel_name = (uu___339_2564.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___339_2564.encode_non_total_function_typ);
          current_module_name = (uu___339_2564.current_module_name)
        }  in
      (fname, ftok, uu____2563)
  
let try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___314_2627  ->
           match uu___314_2627 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2666 -> FStar_Pervasives_Native.None)
  
let contains_name : env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____2683 =
        lookup_binding env
          (fun uu___315_2691  ->
             match uu___315_2691 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2706 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2683 FStar_Option.isSome
  
let lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____2725 = try_lookup_lid env a  in
      match uu____2725 with
      | FStar_Pervasives_Native.None  ->
          let uu____2758 =
            let uu____2759 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2759  in
          failwith uu____2758
      | FStar_Pervasives_Native.Some s -> s
  
let push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___340_2807 = env  in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___340_2807.depth);
            tcenv = (uu___340_2807.tcenv);
            warn = (uu___340_2807.warn);
            cache = (uu___340_2807.cache);
            nolabels = (uu___340_2807.nolabels);
            use_zfuel_name = (uu___340_2807.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___340_2807.encode_non_total_function_typ);
            current_module_name = (uu___340_2807.current_module_name)
          }
  
let push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2821 = lookup_lid env x  in
        match uu____2821 with
        | (t1,t2,uu____2834) ->
            let t3 =
              let uu____2844 =
                let uu____2851 =
                  let uu____2854 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____2854]  in
                (f, uu____2851)  in
              FStar_SMTEncoding_Util.mkApp uu____2844  in
            let uu___341_2859 = env  in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___341_2859.depth);
              tcenv = (uu___341_2859.tcenv);
              warn = (uu___341_2859.warn);
              cache = (uu___341_2859.cache);
              nolabels = (uu___341_2859.nolabels);
              use_zfuel_name = (uu___341_2859.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___341_2859.encode_non_total_function_typ);
              current_module_name = (uu___341_2859.current_module_name)
            }
  
let try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____2872 = try_lookup_lid env l  in
      match uu____2872 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2921 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2929,fuel::[]) ->
                         let uu____2933 =
                           let uu____2934 =
                             let uu____2935 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2935
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2934 "fuel"  in
                         if uu____2933
                         then
                           let uu____2938 =
                             let uu____2939 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2939
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____2938
                         else FStar_Pervasives_Native.Some t
                     | uu____2943 -> FStar_Pervasives_Native.Some t)
                | uu____2944 -> FStar_Pervasives_Native.None))
  
let lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term
  =
  fun env  ->
    fun a  ->
      let uu____2957 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2957 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2961 =
            let uu____2962 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2962  in
          failwith uu____2961
  
let lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string
  =
  fun env  ->
    fun a  ->
      let uu____2973 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____2973 with | (x,uu____2985,uu____2986) -> x
  
let lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun a  ->
      let uu____3011 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____3011 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____3047;
                 FStar_SMTEncoding_Term.rng = uu____3048;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____3063 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____3087 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___316_3103  ->
           match uu___316_3103 with
           | Binding_fvar (uu____3106,nm',tok,uu____3109) when nm = nm' ->
               tok
           | uu____3118 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____3122 .
    'Auu____3122 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____3140  ->
      match uu____3140 with
      | (pats,vars,body) ->
          let fallback uu____3165 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____3170 = FStar_Options.unthrottle_inductives ()  in
          if uu____3170
          then fallback ()
          else
            (let uu____3172 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____3172 with
             | (fsym,fterm) ->
                 let add_fuel1 tms =
                   FStar_All.pipe_right tms
                     (FStar_List.map
                        (fun p  ->
                           match p.FStar_SMTEncoding_Term.tm with
                           | FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var "HasType",args) ->
                               FStar_SMTEncoding_Util.mkApp
                                 ("HasTypeFuel", (fterm :: args))
                           | uu____3203 -> p))
                    in
                 let pats1 = FStar_List.map add_fuel1 pats  in
                 let body1 =
                   match body.FStar_SMTEncoding_Term.tm with
                   | FStar_SMTEncoding_Term.App
                       (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                       let guard1 =
                         match guard.FStar_SMTEncoding_Term.tm with
                         | FStar_SMTEncoding_Term.App
                             (FStar_SMTEncoding_Term.And ,guards) ->
                             let uu____3224 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____3224
                         | uu____3227 ->
                             let uu____3228 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____3228 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____3233 -> body  in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                    in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1") 
let head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3274 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3287 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3294 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3295 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3312 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3329 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3331 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3331 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3349;
             FStar_Syntax_Syntax.vars = uu____3350;_},uu____3351)
          ->
          let uu____3372 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3372 FStar_Option.isNone
      | uu____3389 -> false
  
let head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____3396 =
        let uu____3397 = FStar_Syntax_Util.un_uinst t  in
        uu____3397.FStar_Syntax_Syntax.n  in
      match uu____3396 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3400,uu____3401,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___317_3422  ->
                  match uu___317_3422 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3423 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3425 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3425 FStar_Option.isSome
      | uu____3442 -> false
  
let whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____3449 = head_normal env t  in
      if uu____3449
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Weak;
          FStar_TypeChecker_Normalize.HNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let norm : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____3460 =
      let uu____3461 = FStar_Syntax_Syntax.null_binder t  in [uu____3461]  in
    let uu____3462 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3460 uu____3462 FStar_Pervasives_Native.None
  
let mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3500 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3500
                | s ->
                    let uu____3505 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3505) e)
  
let mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let is_app : FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___318_3520  ->
    match uu___318_3520 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3521 -> false
  
let is_an_eta_expansion :
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun vars  ->
      fun body  ->
        let rec check_partial_applications t xs =
          match ((t.FStar_SMTEncoding_Term.tm), xs) with
          | (FStar_SMTEncoding_Term.App
             (app,f::{
                       FStar_SMTEncoding_Term.tm =
                         FStar_SMTEncoding_Term.FreeV y;
                       FStar_SMTEncoding_Term.freevars = uu____3557;
                       FStar_SMTEncoding_Term.rng = uu____3558;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3581) ->
              let uu____3590 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3601 -> false) args (FStar_List.rev xs))
                 in
              if uu____3590
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3605,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3609 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3613 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3613))
                 in
              if uu____3609
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3617 -> FStar_Pervasives_Native.None  in
        check_partial_applications body (FStar_List.rev vars)
  
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3[@@deriving show]
type labels = label Prims.list[@@deriving show]
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
    ;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
    ;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term ;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
    }[@@deriving show]
let __proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let __proj__Mkpattern__item__pat_term :
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let __proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let __proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
exception Let_rec_unencodeable 
let uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____3839 -> false
  
exception Inner_let_rec 
let uu___is_Inner_let_rec : Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3843 -> false
  
let as_function_typ :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3862 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3875 ->
            let uu____3882 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____3882
        | uu____3883 ->
            if norm1
            then let uu____3884 = whnf env t1  in aux false uu____3884
            else
              (let uu____3886 =
                 let uu____3887 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____3888 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3887 uu____3888
                  in
               failwith uu____3886)
         in
      aux true t0
  
let rec curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3920) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3925 ->
        let uu____3926 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3926)
  
let is_arithmetic_primitive :
  'Auu____3940 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3940 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3960::uu____3961::[]) ->
          ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition)
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.op_Subtraction))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.op_Multiply))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
            ||
            (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3965::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3968 -> false
  
let isInteger : FStar_Syntax_Syntax.term' -> Prims.bool =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3989 -> false
  
let getInteger : FStar_Syntax_Syntax.term' -> Prims.int =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____4004 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____4008 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____4008)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____4047)::uu____4048::uu____4049::[]) ->
          (((((((((((FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_and_lid)
                      ||
                      (FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Parser_Const.bv_xor_lid))
                     ||
                     (FStar_Syntax_Syntax.fv_eq_lid fv
                        FStar_Parser_Const.bv_or_lid))
                    ||
                    (FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.bv_add_lid))
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.bv_sub_lid))
                  ||
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_shift_left_lid))
                 ||
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_shift_right_lid))
                ||
                (FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.bv_udiv_lid))
               ||
               (FStar_Syntax_Syntax.fv_eq_lid fv
                  FStar_Parser_Const.bv_mod_lid))
              ||
              (FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.bv_uext_lid))
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.bv_mul_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____4100)::uu____4101::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____4138 -> false
  
let rec encode_const :
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4357 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4357, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4360 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4360, [])
      | FStar_Const.Const_char c1 ->
          let uu____4364 =
            let uu____4365 =
              let uu____4372 =
                let uu____4375 =
                  let uu____4376 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4376  in
                [uu____4375]  in
              ("FStar.Char.__char_of_int", uu____4372)  in
            FStar_SMTEncoding_Util.mkApp uu____4365  in
          (uu____4364, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4392 =
            let uu____4393 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4393  in
          (uu____4392, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4414) ->
          let uu____4415 = varops.string_const s  in (uu____4415, [])
      | FStar_Const.Const_range uu____4418 ->
          let uu____4419 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4419, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4425 =
            let uu____4426 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4426  in
          failwith uu____4425

and encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4455 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4455
         then
           let uu____4456 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4456
         else ());
        (let uu____4458 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4542  ->
                   fun b  ->
                     match uu____4542 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4621 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4637 = gen_term_var env1 x  in
                           match uu____4637 with
                           | (xxsym,xx,env') ->
                               let uu____4661 =
                                 let uu____4666 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4666 env1 xx
                                  in
                               (match uu____4661 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4621 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4458 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4825 = encode_term t env  in
          match uu____4825 with
          | (t1,decls) ->
              let uu____4836 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____4836, decls)

and encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4847 = encode_term t env  in
          match uu____4847 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4862 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____4862, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4864 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____4864, decls))

and encode_arith_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4870 = encode_args args_e env  in
        match uu____4870 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4889 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____4898 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____4898  in
            let binary arg_tms1 =
              let uu____4911 =
                let uu____4912 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____4912  in
              let uu____4913 =
                let uu____4914 =
                  let uu____4915 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____4915  in
                FStar_SMTEncoding_Term.unboxInt uu____4914  in
              (uu____4911, uu____4913)  in
            let mk_default uu____4921 =
              let uu____4922 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4922 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms))
               in
            let mk_l op mk_args ts =
              let uu____4973 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____4973
              then
                let uu____4974 =
                  let uu____4975 = mk_args ts  in op uu____4975  in
                FStar_All.pipe_right uu____4974 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____5004 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____5004
              then
                let uu____5005 = binary ts  in
                match uu____5005 with
                | (t1,t2) ->
                    let uu____5012 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____5012
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____5016 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____5016
                 then
                   let uu____5017 = op (binary ts)  in
                   FStar_All.pipe_right uu____5017
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ())
               in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary  in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary  in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary  in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul  in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv  in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod  in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)]  in
            let uu____5148 =
              let uu____5157 =
                FStar_List.tryFind
                  (fun uu____5179  ->
                     match uu____5179 with
                     | (l,uu____5189) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____5157 FStar_Util.must  in
            (match uu____5148 with
             | (uu____5228,op) ->
                 let uu____5238 = op arg_tms  in (uu____5238, decls))

and encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____5246 = FStar_List.hd args_e  in
        match uu____5246 with
        | (tm_sz,uu____5254) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5264 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5264 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
                  ((let uu____5272 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5272);
                   t_decls)
               in
            let uu____5273 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5293::(sz_arg,uu____5295)::uu____5296::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5345 =
                    let uu____5348 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5348  in
                  let uu____5351 =
                    let uu____5354 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5354  in
                  (uu____5345, uu____5351)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5360::(sz_arg,uu____5362)::uu____5363::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5412 =
                    let uu____5413 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5413
                     in
                  failwith uu____5412
              | uu____5422 ->
                  let uu____5429 = FStar_List.tail args_e  in
                  (uu____5429, FStar_Pervasives_Native.None)
               in
            (match uu____5273 with
             | (arg_tms,ext_sz) ->
                 let uu____5452 = encode_args arg_tms env  in
                 (match uu____5452 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5473 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5482 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5482  in
                      let unary_arith arg_tms2 =
                        let uu____5491 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5491  in
                      let binary arg_tms2 =
                        let uu____5504 =
                          let uu____5505 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5505
                           in
                        let uu____5506 =
                          let uu____5507 =
                            let uu____5508 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5508  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5507
                           in
                        (uu____5504, uu____5506)  in
                      let binary_arith arg_tms2 =
                        let uu____5523 =
                          let uu____5524 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5524
                           in
                        let uu____5525 =
                          let uu____5526 =
                            let uu____5527 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5527  in
                          FStar_SMTEncoding_Term.unboxInt uu____5526  in
                        (uu____5523, uu____5525)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____5576 =
                          let uu____5577 = mk_args ts  in op uu____5577  in
                        FStar_All.pipe_right uu____5576 resBox  in
                      let bv_and =
                        mk_bv FStar_SMTEncoding_Util.mkBvAnd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_xor =
                        mk_bv FStar_SMTEncoding_Util.mkBvXor binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_or =
                        mk_bv FStar_SMTEncoding_Util.mkBvOr binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_add =
                        mk_bv FStar_SMTEncoding_Util.mkBvAdd binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_sub =
                        mk_bv FStar_SMTEncoding_Util.mkBvSub binary
                          (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shl =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShl sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_shr =
                        mk_bv (FStar_SMTEncoding_Util.mkBvShr sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_udiv =
                        mk_bv (FStar_SMTEncoding_Util.mkBvUdiv sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mod =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMod sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_mul =
                        mk_bv (FStar_SMTEncoding_Util.mkBvMul sz)
                          binary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let bv_ult =
                        mk_bv FStar_SMTEncoding_Util.mkBvUlt binary
                          FStar_SMTEncoding_Term.boxBool
                         in
                      let bv_uext arg_tms2 =
                        let uu____5685 =
                          let uu____5688 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____5688  in
                        let uu____5690 =
                          let uu____5693 =
                            let uu____5694 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____5694  in
                          FStar_SMTEncoding_Term.boxBitVec uu____5693  in
                        mk_bv uu____5685 unary uu____5690 arg_tms2  in
                      let to_int1 =
                        mk_bv FStar_SMTEncoding_Util.mkBvToNat unary
                          FStar_SMTEncoding_Term.boxInt
                         in
                      let bv_to =
                        mk_bv (FStar_SMTEncoding_Util.mkNatToBv sz)
                          unary_arith (FStar_SMTEncoding_Term.boxBitVec sz)
                         in
                      let ops =
                        [(FStar_Parser_Const.bv_and_lid, bv_and);
                        (FStar_Parser_Const.bv_xor_lid, bv_xor);
                        (FStar_Parser_Const.bv_or_lid, bv_or);
                        (FStar_Parser_Const.bv_add_lid, bv_add);
                        (FStar_Parser_Const.bv_sub_lid, bv_sub);
                        (FStar_Parser_Const.bv_shift_left_lid, bv_shl);
                        (FStar_Parser_Const.bv_shift_right_lid, bv_shr);
                        (FStar_Parser_Const.bv_udiv_lid, bv_udiv);
                        (FStar_Parser_Const.bv_mod_lid, bv_mod);
                        (FStar_Parser_Const.bv_mul_lid, bv_mul);
                        (FStar_Parser_Const.bv_ult_lid, bv_ult);
                        (FStar_Parser_Const.bv_uext_lid, bv_uext);
                        (FStar_Parser_Const.bv_to_nat_lid, to_int1);
                        (FStar_Parser_Const.nat_to_bv_lid, bv_to)]  in
                      let uu____5893 =
                        let uu____5902 =
                          FStar_List.tryFind
                            (fun uu____5924  ->
                               match uu____5924 with
                               | (l,uu____5934) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____5902 FStar_Util.must  in
                      (match uu____5893 with
                       | (uu____5975,op) ->
                           let uu____5985 = op arg_tms1  in
                           (uu____5985, (FStar_List.append sz_decls decls)))))

and encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____5996 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____5996
       then
         let uu____5997 = FStar_Syntax_Print.tag_of_term t  in
         let uu____5998 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____5999 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5997 uu____5998
           uu____5999
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____6005 ->
           let uu____6030 =
             let uu____6031 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6032 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6033 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6034 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6031
               uu____6032 uu____6033 uu____6034
              in
           failwith uu____6030
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____6039 =
             let uu____6040 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____6041 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____6042 = FStar_Syntax_Print.term_to_string t0  in
             let uu____6043 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____6040
               uu____6041 uu____6042 uu____6043
              in
           failwith uu____6039
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____6049 =
             let uu____6050 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____6050
              in
           failwith uu____6049
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____6057) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____6098;
              FStar_Syntax_Syntax.vars = uu____6099;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____6116 = varops.fresh "t"  in
             (uu____6116, FStar_SMTEncoding_Term.Term_sort)  in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym  in
           let decl =
             let uu____6119 =
               let uu____6130 =
                 let uu____6133 = FStar_Util.format1 "alien term (%s)" desc
                    in
                 FStar_Pervasives_Native.Some uu____6133  in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____6130)
                in
             FStar_SMTEncoding_Term.DeclFun uu____6119  in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____6141) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____6151 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____6151, [])
       | FStar_Syntax_Syntax.Tm_type uu____6154 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____6158) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____6183 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____6183 with
            | (binders1,res) ->
                let uu____6194 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____6194
                then
                  let uu____6199 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____6199 with
                   | (vars,guards,env',decls,uu____6224) ->
                       let fsym =
                         let uu____6242 = varops.fresh "f"  in
                         (uu____6242, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____6245 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___342_6254 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___342_6254.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___342_6254.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___342_6254.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___342_6254.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___342_6254.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___342_6254.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___342_6254.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___342_6254.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___342_6254.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___342_6254.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___342_6254.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___342_6254.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___342_6254.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___342_6254.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___342_6254.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___342_6254.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___342_6254.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___342_6254.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___342_6254.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___342_6254.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___342_6254.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___342_6254.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___342_6254.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___342_6254.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___342_6254.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___342_6254.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___342_6254.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___342_6254.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___342_6254.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___342_6254.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___342_6254.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___342_6254.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___342_6254.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____6245 with
                        | (pre_opt,res_t) ->
                            let uu____6265 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6265 with
                             | (res_pred,decls') ->
                                 let uu____6276 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6289 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6289, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6293 =
                                         encode_formula pre env'  in
                                       (match uu____6293 with
                                        | (guard,decls0) ->
                                            let uu____6306 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6306, decls0))
                                    in
                                 (match uu____6276 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6318 =
                                          let uu____6329 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6329)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6318
                                         in
                                      let cvars =
                                        let uu____6347 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6347
                                          (FStar_List.filter
                                             (fun uu____6361  ->
                                                match uu____6361 with
                                                | (x,uu____6367) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym)))
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____6386 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6386 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6394 =
                                             let uu____6395 =
                                               let uu____6402 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6402)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6395
                                              in
                                           (uu____6394,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6422 =
                                               let uu____6423 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6423
                                                in
                                             varops.mk_unique uu____6422  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____6434 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____6434
                                             then
                                               let uu____6437 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6437
                                             else
                                               FStar_Pervasives_Native.None
                                              in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption)
                                              in
                                           let t1 =
                                             let uu____6445 =
                                               let uu____6452 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6452)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6445
                                              in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type
                                              in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym
                                                in
                                             let uu____6464 =
                                               let uu____6471 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6471,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6464
                                              in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1
                                              in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1
                                              in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym
                                                in
                                             let uu____6492 =
                                               let uu____6499 =
                                                 let uu____6500 =
                                                   let uu____6511 =
                                                     let uu____6512 =
                                                       let uu____6517 =
                                                         let uu____6518 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6518
                                                          in
                                                       (f_has_t, uu____6517)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6512
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6511)
                                                    in
                                                 mkForall_fuel uu____6500  in
                                               (uu____6499,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6492
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6541 =
                                               let uu____6548 =
                                                 let uu____6549 =
                                                   let uu____6560 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6560)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6549
                                                  in
                                               (uu____6548,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6541
                                              in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1]))
                                              in
                                           ((let uu____6585 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6585);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow"  in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None)
                      in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, [])  in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym  in
                     let uu____6600 =
                       let uu____6607 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6607,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6600  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6619 =
                       let uu____6626 =
                         let uu____6627 =
                           let uu____6638 =
                             let uu____6639 =
                               let uu____6644 =
                                 let uu____6645 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6645
                                  in
                               (f_has_t, uu____6644)  in
                             FStar_SMTEncoding_Util.mkImp uu____6639  in
                           ([[f_has_t]], [fsym], uu____6638)  in
                         mkForall_fuel uu____6627  in
                       (uu____6626, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6619  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6672 ->
           let uu____6679 =
             let uu____6684 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6684 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6691;
                 FStar_Syntax_Syntax.vars = uu____6692;_} ->
                 let uu____6699 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6699 with
                  | (b,f1) ->
                      let uu____6724 =
                        let uu____6725 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6725  in
                      (uu____6724, f1))
             | uu____6734 -> failwith "impossible"  in
           (match uu____6679 with
            | (x,f) ->
                let uu____6745 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6745 with
                 | (base_t,decls) ->
                     let uu____6756 = gen_term_var env x  in
                     (match uu____6756 with
                      | (x1,xtm,env') ->
                          let uu____6770 = encode_formula f env'  in
                          (match uu____6770 with
                           | (refinement,decls') ->
                               let uu____6781 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6781 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t
                                       in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement)
                                       in
                                    let cvars =
                                      let uu____6797 =
                                        let uu____6800 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6807 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6800
                                          uu____6807
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6797
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6840  ->
                                              match uu____6840 with
                                              | (y,uu____6846) ->
                                                  (y <> x1) && (y <> fsym)))
                                       in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort)
                                       in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding)
                                       in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey
                                       in
                                    let uu____6879 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____6879 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6887 =
                                           let uu____6888 =
                                             let uu____6895 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6895)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6888
                                            in
                                         (uu____6887,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____6916 =
                                             let uu____6917 =
                                               let uu____6918 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6918
                                                in
                                             Prims.strcat module_name
                                               uu____6917
                                              in
                                           varops.mk_unique uu____6916  in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1
                                            in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                            in
                                         let t1 =
                                           let uu____6932 =
                                             let uu____6939 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____6939)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6932
                                            in
                                         let x_has_base_t =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             xtm base_t
                                            in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1
                                            in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type
                                            in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t
                                            in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1
                                            in
                                         let t_haseq1 =
                                           let uu____6954 =
                                             let uu____6961 =
                                               let uu____6962 =
                                                 let uu____6973 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6973)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6962
                                                in
                                             (uu____6961,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6954
                                            in
                                         let t_kinding =
                                           let uu____6991 =
                                             let uu____6998 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____6998,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6991
                                            in
                                         let t_interp =
                                           let uu____7016 =
                                             let uu____7023 =
                                               let uu____7024 =
                                                 let uu____7035 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____7035)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____7024
                                                in
                                             let uu____7058 =
                                               let uu____7061 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____7061
                                                in
                                             (uu____7023, uu____7058,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____7016
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____7068 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____7068);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____7098 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____7098  in
           let uu____7099 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____7099 with
            | (t_has_k,decls) ->
                let d =
                  let uu____7111 =
                    let uu____7118 =
                      let uu____7119 =
                        let uu____7120 =
                          let uu____7121 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____7121
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____7120  in
                      varops.mk_unique uu____7119  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____7118)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____7111  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____7126 ->
           let uu____7141 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____7141 with
            | (head1,args_e) ->
                let uu____7182 =
                  let uu____7195 =
                    let uu____7196 = FStar_Syntax_Subst.compress head1  in
                    uu____7196.FStar_Syntax_Syntax.n  in
                  (uu____7195, args_e)  in
                (match uu____7182 with
                 | uu____7211 when head_redex env head1 ->
                     let uu____7224 = whnf env t  in
                     encode_term uu____7224 env
                 | uu____7225 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____7244 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7258;
                       FStar_Syntax_Syntax.vars = uu____7259;_},uu____7260),uu____7261::
                    (v1,uu____7263)::(v2,uu____7265)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7316 = encode_term v1 env  in
                     (match uu____7316 with
                      | (v11,decls1) ->
                          let uu____7327 = encode_term v2 env  in
                          (match uu____7327 with
                           | (v21,decls2) ->
                               let uu____7338 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7338,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7342::(v1,uu____7344)::(v2,uu____7346)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7393 = encode_term v1 env  in
                     (match uu____7393 with
                      | (v11,decls1) ->
                          let uu____7404 = encode_term v2 env  in
                          (match uu____7404 with
                           | (v21,decls2) ->
                               let uu____7415 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7415,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7419)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(rng,uu____7445)::(arg,uu____7447)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7482) ->
                     let e0 =
                       let uu____7500 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7500
                        in
                     ((let uu____7508 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7508
                       then
                         let uu____7509 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7509
                       else ());
                      (let e =
                         let uu____7514 =
                           let uu____7515 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7516 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7515
                             uu____7516
                            in
                         uu____7514 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7525),(arg,uu____7527)::[]) -> encode_term arg env
                 | uu____7552 ->
                     let uu____7565 = encode_args args_e env  in
                     (match uu____7565 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7620 = encode_term head1 env  in
                            match uu____7620 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7684 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7684 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7762  ->
                                                 fun uu____7763  ->
                                                   match (uu____7762,
                                                           uu____7763)
                                                   with
                                                   | ((bv,uu____7785),
                                                      (a,uu____7787)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____7805 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____7805
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____7810 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____7810 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____7825 =
                                                   let uu____7832 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____7841 =
                                                     let uu____7842 =
                                                       let uu____7843 =
                                                         let uu____7844 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____7844
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7843
                                                        in
                                                     varops.mk_unique
                                                       uu____7842
                                                      in
                                                   (uu____7832,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7841)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7825
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____7861 = lookup_free_var_sym env fv  in
                            match uu____7861 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args))
                                   in
                                (tm, decls)
                             in
                          let head2 = FStar_Syntax_Subst.compress head1  in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.pos = uu____7892;
                                   FStar_Syntax_Syntax.vars = uu____7893;_},uu____7894)
                                ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                FStar_Pervasives_Native.Some
                                  (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_fvar fv;
                                   FStar_Syntax_Syntax.pos = uu____7905;
                                   FStar_Syntax_Syntax.vars = uu____7906;_},uu____7907)
                                ->
                                let uu____7912 =
                                  let uu____7913 =
                                    let uu____7918 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7918
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7913
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7912
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7948 =
                                  let uu____7949 =
                                    let uu____7954 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7954
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7949
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7948
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7983,(FStar_Util.Inl t1,uu____7985),uu____7986)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____8035,(FStar_Util.Inr c,uu____8037),uu____8038)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____8087 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____8114 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____8114
                                  in
                               let uu____8115 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____8115 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____8131;
                                            FStar_Syntax_Syntax.vars =
                                              uu____8132;_},uu____8133)
                                         when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____8147 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (FStar_Pervasives_Native.Some
                                                (formals, c))
                                         else
                                           encode_partial_app
                                             FStar_Pervasives_Native.None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____8196 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____8196 with
            | (bs1,body1,opening) ->
                let fallback uu____8219 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____8226 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____8226, [decl])  in
                let is_impure rc =
                  let uu____8233 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____8233 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____8243 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____8243
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8263 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8263
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8267 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8267)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8274 =
                         let uu____8279 =
                           let uu____8280 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8280
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8279)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8274);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8282 =
                       (is_impure rc) &&
                         (let uu____8284 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8284)
                        in
                     if uu____8282
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8291 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8291 with
                        | (vars,guards,envbody,decls,uu____8316) ->
                            let body2 =
                              let uu____8330 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8330
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8332 = encode_term body2 envbody  in
                            (match uu____8332 with
                             | (body3,decls') ->
                                 let uu____8343 =
                                   let uu____8352 = codomain_eff rc  in
                                   match uu____8352 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8371 = encode_term tfun env
                                          in
                                       (match uu____8371 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8343 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8403 =
                                          let uu____8414 =
                                            let uu____8415 =
                                              let uu____8420 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8420, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8415
                                             in
                                          ([], vars, uu____8414)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8403
                                         in
                                      let cvars =
                                        FStar_SMTEncoding_Term.free_variables
                                          key_body
                                         in
                                      let cvars1 =
                                        match arrow_t_opt with
                                        | FStar_Pervasives_Native.None  ->
                                            cvars
                                        | FStar_Pervasives_Native.Some t1 ->
                                            let uu____8432 =
                                              let uu____8435 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8435
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8432
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8454 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8454 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8462 =
                                             let uu____8463 =
                                               let uu____8470 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8470)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8463
                                              in
                                           (uu____8462,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8481 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8481 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8492 =
                                                    let uu____8493 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8493 = cache_size
                                                     in
                                                  if uu____8492
                                                  then []
                                                  else
                                                    FStar_List.append decls
                                                      (FStar_List.append
                                                         decls' decls'')
                                                   in
                                                (t1, decls1)
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let cvar_sorts =
                                                  FStar_List.map
                                                    FStar_Pervasives_Native.snd
                                                    cvars1
                                                   in
                                                let fsym =
                                                  let module_name =
                                                    env.current_module_name
                                                     in
                                                  let fsym =
                                                    let uu____8509 =
                                                      let uu____8510 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8510
                                                       in
                                                    varops.mk_unique
                                                      uu____8509
                                                     in
                                                  Prims.strcat module_name
                                                    (Prims.strcat "_" fsym)
                                                   in
                                                let fdecl =
                                                  FStar_SMTEncoding_Term.DeclFun
                                                    (fsym, cvar_sorts,
                                                      FStar_SMTEncoding_Term.Term_sort,
                                                      FStar_Pervasives_Native.None)
                                                   in
                                                let f =
                                                  let uu____8517 =
                                                    let uu____8524 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8524)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8517
                                                   in
                                                let app = mk_Apply f vars  in
                                                let typing_f =
                                                  match arrow_t_opt with
                                                  | FStar_Pervasives_Native.None
                                                       -> []
                                                  | FStar_Pervasives_Native.Some
                                                      t1 ->
                                                      let f_has_t =
                                                        FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                          FStar_Pervasives_Native.None
                                                          f t1
                                                         in
                                                      let a_name =
                                                        Prims.strcat
                                                          "typing_" fsym
                                                         in
                                                      let uu____8542 =
                                                        let uu____8543 =
                                                          let uu____8550 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8550,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8543
                                                         in
                                                      [uu____8542]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8563 =
                                                    let uu____8570 =
                                                      let uu____8571 =
                                                        let uu____8582 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8582)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8571
                                                       in
                                                    (uu____8570,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8563
                                                   in
                                                let f_decls =
                                                  FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls''
                                                          (FStar_List.append
                                                             (fdecl ::
                                                             typing_f)
                                                             [interp_f])))
                                                   in
                                                ((let uu____8599 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8599);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8602,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8603;
                          FStar_Syntax_Syntax.lbunivs = uu____8604;
                          FStar_Syntax_Syntax.lbtyp = uu____8605;
                          FStar_Syntax_Syntax.lbeff = uu____8606;
                          FStar_Syntax_Syntax.lbdef = uu____8607;_}::uu____8608),uu____8609)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8635;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8637;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8658 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and encode_let :
  FStar_Syntax_Syntax.bv ->
    FStar_Syntax_Syntax.typ ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          env_t ->
            (FStar_Syntax_Syntax.term ->
               env_t ->
                 (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                   FStar_Pervasives_Native.tuple2)
              ->
              (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____8728 = encode_term e1 env  in
              match uu____8728 with
              | (ee1,decls1) ->
                  let uu____8739 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8739 with
                   | (xs,e21) ->
                       let uu____8764 = FStar_List.hd xs  in
                       (match uu____8764 with
                        | (x1,uu____8778) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____8780 = encode_body e21 env'  in
                            (match uu____8780 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and encode_match :
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
                 FStar_Pervasives_Native.tuple2)
            ->
            (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
              FStar_Pervasives_Native.tuple2
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____8812 =
              let uu____8819 =
                let uu____8820 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8820  in
              gen_term_var env uu____8819  in
            match uu____8812 with
            | (scrsym,scr',env1) ->
                let uu____8828 = encode_term e env1  in
                (match uu____8828 with
                 | (scr,decls) ->
                     let uu____8839 =
                       let encode_branch b uu____8864 =
                         match uu____8864 with
                         | (else_case,decls1) ->
                             let uu____8883 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8883 with
                              | (p,w,br) ->
                                  let uu____8909 = encode_pat env1 p  in
                                  (match uu____8909 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8946  ->
                                                   match uu____8946 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____8953 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8975 =
                                               encode_term w1 env2  in
                                             (match uu____8975 with
                                              | (w2,decls2) ->
                                                  let uu____8988 =
                                                    let uu____8989 =
                                                      let uu____8994 =
                                                        let uu____8995 =
                                                          let uu____9000 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____9000)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8995
                                                         in
                                                      (guard, uu____8994)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8989
                                                     in
                                                  (uu____8988, decls2))
                                          in
                                       (match uu____8953 with
                                        | (guard1,decls2) ->
                                            let uu____9013 =
                                              encode_br br env2  in
                                            (match uu____9013 with
                                             | (br1,decls3) ->
                                                 let uu____9026 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____9026,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8839 with
                      | (match_tm,decls1) ->
                          let uu____9045 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____9045, decls1)))

and encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____9085 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____9085
       then
         let uu____9086 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____9086
       else ());
      (let uu____9088 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____9088 with
       | (vars,pat_term) ->
           let uu____9105 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____9158  ->
                     fun v1  ->
                       match uu____9158 with
                       | (env1,vars1) ->
                           let uu____9210 = gen_term_var env1 v1  in
                           (match uu____9210 with
                            | (xx,uu____9232,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____9105 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9311 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9312 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9313 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9321 = encode_const c env1  in
                      (match uu____9321 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9335::uu____9336 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9339 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9362 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9362 with
                        | (uu____9369,uu____9370::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9373 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9406  ->
                                  match uu____9406 with
                                  | (arg,uu____9414) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9420 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9420))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9447) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9478 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9501 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9545  ->
                                  match uu____9545 with
                                  | (arg,uu____9559) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9565 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9565))
                         in
                      FStar_All.pipe_right uu____9501 FStar_List.flatten
                   in
                let pat_term1 uu____9593 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____9603 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9641  ->
                fun uu____9642  ->
                  match (uu____9641, uu____9642) with
                  | ((tms,decls),(t,uu____9678)) ->
                      let uu____9699 = encode_term t env  in
                      (match uu____9699 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9603 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9756 = FStar_Syntax_Util.list_elements e  in
        match uu____9756 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9777 =
          let uu____9792 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9792 FStar_Syntax_Util.head_and_args  in
        match uu____9777 with
        | (head1,args) ->
            let uu____9831 =
              let uu____9844 =
                let uu____9845 = FStar_Syntax_Util.un_uinst head1  in
                uu____9845.FStar_Syntax_Syntax.n  in
              (uu____9844, args)  in
            (match uu____9831 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9859,uu____9860)::(e,uu____9862)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9897 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9933 =
            let uu____9948 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9948 FStar_Syntax_Util.head_and_args
             in
          match uu____9933 with
          | (head1,args) ->
              let uu____9989 =
                let uu____10002 =
                  let uu____10003 = FStar_Syntax_Util.un_uinst head1  in
                  uu____10003.FStar_Syntax_Syntax.n  in
                (uu____10002, args)  in
              (match uu____9989 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____10020)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____10047 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____10069 = smt_pat_or1 t1  in
            (match uu____10069 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____10085 = list_elements1 e  in
                 FStar_All.pipe_right uu____10085
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____10103 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____10103
                           (FStar_List.map one_pat)))
             | uu____10114 ->
                 let uu____10119 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____10119])
        | uu____10140 ->
            let uu____10143 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____10143]
         in
      let uu____10164 =
        let uu____10183 =
          let uu____10184 = FStar_Syntax_Subst.compress t  in
          uu____10184.FStar_Syntax_Syntax.n  in
        match uu____10183 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____10223 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____10223 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10266;
                        FStar_Syntax_Syntax.effect_name = uu____10267;
                        FStar_Syntax_Syntax.result_typ = uu____10268;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10270)::(post,uu____10272)::(pats,uu____10274)::[];
                        FStar_Syntax_Syntax.flags = uu____10275;_}
                      ->
                      let uu____10316 = lemma_pats pats  in
                      (binders1, pre, post, uu____10316)
                  | uu____10333 -> failwith "impos"))
        | uu____10352 -> failwith "Impos"  in
      match uu____10164 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___343_10400 = env  in
            {
              bindings = (uu___343_10400.bindings);
              depth = (uu___343_10400.depth);
              tcenv = (uu___343_10400.tcenv);
              warn = (uu___343_10400.warn);
              cache = (uu___343_10400.cache);
              nolabels = (uu___343_10400.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___343_10400.encode_non_total_function_typ);
              current_module_name = (uu___343_10400.current_module_name)
            }  in
          let uu____10401 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10401 with
           | (vars,guards,env2,decls,uu____10426) ->
               let uu____10439 =
                 let uu____10454 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10508 =
                             let uu____10519 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10519
                               FStar_List.unzip
                              in
                           match uu____10508 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10454 FStar_List.unzip  in
               (match uu____10439 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___344_10671 = env2  in
                      {
                        bindings = (uu___344_10671.bindings);
                        depth = (uu___344_10671.depth);
                        tcenv = (uu___344_10671.tcenv);
                        warn = (uu___344_10671.warn);
                        cache = (uu___344_10671.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___344_10671.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___344_10671.encode_non_total_function_typ);
                        current_module_name =
                          (uu___344_10671.current_module_name)
                      }  in
                    let uu____10672 =
                      let uu____10677 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10677 env3  in
                    (match uu____10672 with
                     | (pre1,decls'') ->
                         let uu____10684 =
                           let uu____10689 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10689 env3  in
                         (match uu____10684 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10699 =
                                let uu____10700 =
                                  let uu____10711 =
                                    let uu____10712 =
                                      let uu____10717 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10717, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10712
                                     in
                                  (pats, vars, uu____10711)  in
                                FStar_SMTEncoding_Util.mkForall uu____10700
                                 in
                              (uu____10699, decls1)))))

and encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let uu____10730 = FStar_Syntax_Util.head_and_args t  in
      match uu____10730 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10789::(x,uu____10791)::(t1,uu____10793)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10840 = encode_term x env  in
               (match uu____10840 with
                | (x1,decls) ->
                    let uu____10853 = encode_term t1 env  in
                    (match uu____10853 with
                     | (t2,decls') ->
                         let uu____10866 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____10866, (FStar_List.append decls decls'))))
           | uu____10869 -> encode_term t env)

and encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10892 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10892
        then
          let uu____10893 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10894 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10893 uu____10894
        else ()  in
      let enc f r l =
        let uu____10927 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10955 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10955 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10927 with
        | (decls,args) ->
            let uu____10984 =
              let uu___345_10985 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___345_10985.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___345_10985.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10984, decls)
         in
      let const_op f r uu____11016 =
        let uu____11029 = f r  in (uu____11029, [])  in
      let un_op f l =
        let uu____11048 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____11048  in
      let bin_op f uu___319_11064 =
        match uu___319_11064 with
        | t1::t2::[] -> f (t1, t2)
        | uu____11075 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____11109 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____11132  ->
                 match uu____11132 with
                 | (t,uu____11146) ->
                     let uu____11147 = encode_formula t env  in
                     (match uu____11147 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____11109 with
        | (decls,phis) ->
            let uu____11176 =
              let uu___346_11177 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___346_11177.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___346_11177.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____11176, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____11238  ->
               match uu____11238 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11257) -> false
                    | uu____11258 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11273 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11273
        else
          (let uu____11287 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11287 r rf)
         in
      let mk_imp1 r uu___320_11312 =
        match uu___320_11312 with
        | (lhs,uu____11318)::(rhs,uu____11320)::[] ->
            let uu____11347 = encode_formula rhs env  in
            (match uu____11347 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11362) ->
                      (l1, decls1)
                  | uu____11367 ->
                      let uu____11368 = encode_formula lhs env  in
                      (match uu____11368 with
                       | (l2,decls2) ->
                           let uu____11379 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11379, (FStar_List.append decls1 decls2)))))
        | uu____11382 -> failwith "impossible"  in
      let mk_ite r uu___321_11403 =
        match uu___321_11403 with
        | (guard,uu____11409)::(_then,uu____11411)::(_else,uu____11413)::[]
            ->
            let uu____11450 = encode_formula guard env  in
            (match uu____11450 with
             | (g,decls1) ->
                 let uu____11461 = encode_formula _then env  in
                 (match uu____11461 with
                  | (t,decls2) ->
                      let uu____11472 = encode_formula _else env  in
                      (match uu____11472 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11486 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11511 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11511  in
      let connectives =
        let uu____11529 =
          let uu____11542 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11542)  in
        let uu____11559 =
          let uu____11574 =
            let uu____11587 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11587)  in
          let uu____11604 =
            let uu____11619 =
              let uu____11634 =
                let uu____11647 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11647)  in
              let uu____11664 =
                let uu____11679 =
                  let uu____11694 =
                    let uu____11707 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11707)  in
                  [uu____11694;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11679  in
              uu____11634 :: uu____11664  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11619  in
          uu____11574 :: uu____11604  in
        uu____11529 :: uu____11559  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____12028 = encode_formula phi' env  in
            (match uu____12028 with
             | (phi2,decls) ->
                 let uu____12039 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____12039, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____12040 ->
            let uu____12047 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____12047 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____12086 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____12086 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____12098;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____12100;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____12121 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____12121 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____12168::(x,uu____12170)::(t,uu____12172)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____12219 = encode_term x env  in
                 (match uu____12219 with
                  | (x1,decls) ->
                      let uu____12230 = encode_term t env  in
                      (match uu____12230 with
                       | (t1,decls') ->
                           let uu____12241 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____12241, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____12246)::(msg,uu____12248)::(phi2,uu____12250)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12295 =
                   let uu____12300 =
                     let uu____12301 = FStar_Syntax_Subst.compress r  in
                     uu____12301.FStar_Syntax_Syntax.n  in
                   let uu____12304 =
                     let uu____12305 = FStar_Syntax_Subst.compress msg  in
                     uu____12305.FStar_Syntax_Syntax.n  in
                   (uu____12300, uu____12304)  in
                 (match uu____12295 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12314))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12320 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12327)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12352 when head_redex env head2 ->
                 let uu____12365 = whnf env phi1  in
                 encode_formula uu____12365 env
             | uu____12366 ->
                 let uu____12379 = encode_term phi1 env  in
                 (match uu____12379 with
                  | (tt,decls) ->
                      let uu____12390 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___347_12393 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___347_12393.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___347_12393.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12390, decls)))
        | uu____12394 ->
            let uu____12395 = encode_term phi1 env  in
            (match uu____12395 with
             | (tt,decls) ->
                 let uu____12406 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___348_12409 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___348_12409.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___348_12409.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12406, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12445 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12445 with
        | (vars,guards,env2,decls,uu____12484) ->
            let uu____12497 =
              let uu____12510 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12562 =
                          let uu____12573 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12613  ->
                                    match uu____12613 with
                                    | (t,uu____12627) ->
                                        encode_smt_pattern t
                                          (let uu___349_12633 = env2  in
                                           {
                                             bindings =
                                               (uu___349_12633.bindings);
                                             depth = (uu___349_12633.depth);
                                             tcenv = (uu___349_12633.tcenv);
                                             warn = (uu___349_12633.warn);
                                             cache = (uu___349_12633.cache);
                                             nolabels =
                                               (uu___349_12633.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___349_12633.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___349_12633.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12573 FStar_List.unzip
                           in
                        match uu____12562 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12510 FStar_List.unzip  in
            (match uu____12497 with
             | (pats,decls') ->
                 let uu____12742 = encode_formula body env2  in
                 (match uu____12742 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12774;
                             FStar_SMTEncoding_Term.rng = uu____12775;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12790 -> guards  in
                      let uu____12795 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12795, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls'')))))
         in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi  in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____12855  ->
                   match uu____12855 with
                   | (x,uu____12861) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x))
            in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____12869 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12881 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12881) uu____12869 tl1
                in
             let uu____12884 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12911  ->
                       match uu____12911 with
                       | (b,uu____12917) ->
                           let uu____12918 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12918))
                in
             (match uu____12884 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12924) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12938 =
                    let uu____12943 =
                      let uu____12944 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12944
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12943)
                     in
                  FStar_Errors.log_issue pos uu____12938)
          in
       let uu____12945 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12945 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12954 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____13012  ->
                     match uu____13012 with
                     | (l,uu____13026) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12954 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____13059,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13099 = encode_q_body env vars pats body  in
             match uu____13099 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____13144 =
                     let uu____13155 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____13155)  in
                   FStar_SMTEncoding_Term.mkForall uu____13144
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____13174 = encode_q_body env vars pats body  in
             match uu____13174 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____13218 =
                   let uu____13219 =
                     let uu____13230 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____13230)  in
                   FStar_SMTEncoding_Term.mkExists uu____13219
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____13218, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
    ;
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let __proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let __proj__Mkprims_t__item__is : prims_t -> FStar_Ident.lident -> Prims.bool
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let prims : prims_t =
  let uu____13323 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13323 with
  | (asym,a) ->
      let uu____13330 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13330 with
       | (xsym,x) ->
           let uu____13337 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13337 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13381 =
                      let uu____13392 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13392, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13381  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13418 =
                      let uu____13425 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13425)  in
                    FStar_SMTEncoding_Util.mkApp uu____13418  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13438 =
                    let uu____13441 =
                      let uu____13444 =
                        let uu____13447 =
                          let uu____13448 =
                            let uu____13455 =
                              let uu____13456 =
                                let uu____13467 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13467)  in
                              FStar_SMTEncoding_Util.mkForall uu____13456  in
                            (uu____13455, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13448  in
                        let uu____13484 =
                          let uu____13487 =
                            let uu____13488 =
                              let uu____13495 =
                                let uu____13496 =
                                  let uu____13507 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13507)  in
                                FStar_SMTEncoding_Util.mkForall uu____13496
                                 in
                              (uu____13495,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13488  in
                          [uu____13487]  in
                        uu____13447 :: uu____13484  in
                      xtok_decl :: uu____13444  in
                    xname_decl :: uu____13441  in
                  (xtok1, uu____13438)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13598 =
                    let uu____13611 =
                      let uu____13620 =
                        let uu____13621 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13621
                         in
                      quant axy uu____13620  in
                    (FStar_Parser_Const.op_Eq, uu____13611)  in
                  let uu____13630 =
                    let uu____13645 =
                      let uu____13658 =
                        let uu____13667 =
                          let uu____13668 =
                            let uu____13669 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13669  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13668
                           in
                        quant axy uu____13667  in
                      (FStar_Parser_Const.op_notEq, uu____13658)  in
                    let uu____13678 =
                      let uu____13693 =
                        let uu____13706 =
                          let uu____13715 =
                            let uu____13716 =
                              let uu____13717 =
                                let uu____13722 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13723 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13722, uu____13723)  in
                              FStar_SMTEncoding_Util.mkLT uu____13717  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13716
                             in
                          quant xy uu____13715  in
                        (FStar_Parser_Const.op_LT, uu____13706)  in
                      let uu____13732 =
                        let uu____13747 =
                          let uu____13760 =
                            let uu____13769 =
                              let uu____13770 =
                                let uu____13771 =
                                  let uu____13776 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13777 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13776, uu____13777)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13771  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13770
                               in
                            quant xy uu____13769  in
                          (FStar_Parser_Const.op_LTE, uu____13760)  in
                        let uu____13786 =
                          let uu____13801 =
                            let uu____13814 =
                              let uu____13823 =
                                let uu____13824 =
                                  let uu____13825 =
                                    let uu____13830 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13831 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13830, uu____13831)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13825  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13824
                                 in
                              quant xy uu____13823  in
                            (FStar_Parser_Const.op_GT, uu____13814)  in
                          let uu____13840 =
                            let uu____13855 =
                              let uu____13868 =
                                let uu____13877 =
                                  let uu____13878 =
                                    let uu____13879 =
                                      let uu____13884 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13885 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13884, uu____13885)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13879
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13878
                                   in
                                quant xy uu____13877  in
                              (FStar_Parser_Const.op_GTE, uu____13868)  in
                            let uu____13894 =
                              let uu____13909 =
                                let uu____13922 =
                                  let uu____13931 =
                                    let uu____13932 =
                                      let uu____13933 =
                                        let uu____13938 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13939 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13938, uu____13939)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13933
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13932
                                     in
                                  quant xy uu____13931  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13922)
                                 in
                              let uu____13948 =
                                let uu____13963 =
                                  let uu____13976 =
                                    let uu____13985 =
                                      let uu____13986 =
                                        let uu____13987 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13987
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13986
                                       in
                                    quant qx uu____13985  in
                                  (FStar_Parser_Const.op_Minus, uu____13976)
                                   in
                                let uu____13996 =
                                  let uu____14011 =
                                    let uu____14024 =
                                      let uu____14033 =
                                        let uu____14034 =
                                          let uu____14035 =
                                            let uu____14040 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____14041 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____14040, uu____14041)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____14035
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____14034
                                         in
                                      quant xy uu____14033  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____14024)
                                     in
                                  let uu____14050 =
                                    let uu____14065 =
                                      let uu____14078 =
                                        let uu____14087 =
                                          let uu____14088 =
                                            let uu____14089 =
                                              let uu____14094 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____14095 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____14094, uu____14095)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____14089
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____14088
                                           in
                                        quant xy uu____14087  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____14078)
                                       in
                                    let uu____14104 =
                                      let uu____14119 =
                                        let uu____14132 =
                                          let uu____14141 =
                                            let uu____14142 =
                                              let uu____14143 =
                                                let uu____14148 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____14149 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____14148, uu____14149)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____14143
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____14142
                                             in
                                          quant xy uu____14141  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____14132)
                                         in
                                      let uu____14158 =
                                        let uu____14173 =
                                          let uu____14186 =
                                            let uu____14195 =
                                              let uu____14196 =
                                                let uu____14197 =
                                                  let uu____14202 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____14203 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____14202, uu____14203)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____14197
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____14196
                                               in
                                            quant xy uu____14195  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____14186)
                                           in
                                        let uu____14212 =
                                          let uu____14227 =
                                            let uu____14240 =
                                              let uu____14249 =
                                                let uu____14250 =
                                                  let uu____14251 =
                                                    let uu____14256 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____14257 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____14256,
                                                      uu____14257)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14251
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14250
                                                 in
                                              quant xy uu____14249  in
                                            (FStar_Parser_Const.op_And,
                                              uu____14240)
                                             in
                                          let uu____14266 =
                                            let uu____14281 =
                                              let uu____14294 =
                                                let uu____14303 =
                                                  let uu____14304 =
                                                    let uu____14305 =
                                                      let uu____14310 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14311 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14310,
                                                        uu____14311)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14305
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14304
                                                   in
                                                quant xy uu____14303  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14294)
                                               in
                                            let uu____14320 =
                                              let uu____14335 =
                                                let uu____14348 =
                                                  let uu____14357 =
                                                    let uu____14358 =
                                                      let uu____14359 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14359
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14358
                                                     in
                                                  quant qx uu____14357  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14348)
                                                 in
                                              [uu____14335]  in
                                            uu____14281 :: uu____14320  in
                                          uu____14227 :: uu____14266  in
                                        uu____14173 :: uu____14212  in
                                      uu____14119 :: uu____14158  in
                                    uu____14065 :: uu____14104  in
                                  uu____14011 :: uu____14050  in
                                uu____13963 :: uu____13996  in
                              uu____13909 :: uu____13948  in
                            uu____13855 :: uu____13894  in
                          uu____13801 :: uu____13840  in
                        uu____13747 :: uu____13786  in
                      uu____13693 :: uu____13732  in
                    uu____13645 :: uu____13678  in
                  uu____13598 :: uu____13630  in
                let mk1 l v1 =
                  let uu____14573 =
                    let uu____14582 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14640  ->
                              match uu____14640 with
                              | (l',uu____14654) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14582
                      (FStar_Option.map
                         (fun uu____14714  ->
                            match uu____14714 with | (uu____14733,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14573 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14804  ->
                          match uu____14804 with
                          | (l',uu____14818) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____14856 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14856 with
        | (xxsym,xx) ->
            let uu____14863 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14863 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14873 =
                   let uu____14880 =
                     let uu____14881 =
                       let uu____14892 =
                         let uu____14893 =
                           let uu____14898 =
                             let uu____14899 =
                               let uu____14904 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14904)  in
                             FStar_SMTEncoding_Util.mkEq uu____14899  in
                           (xx_has_type, uu____14898)  in
                         FStar_SMTEncoding_Util.mkImp uu____14893  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14892)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14881  in
                   let uu____14929 =
                     let uu____14930 =
                       let uu____14931 =
                         let uu____14932 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14932  in
                       Prims.strcat module_name uu____14931  in
                     varops.mk_unique uu____14930  in
                   (uu____14880, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14929)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14873)
  
let primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____14968 =
      let uu____14969 =
        let uu____14976 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14976, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14969  in
    let uu____14979 =
      let uu____14982 =
        let uu____14983 =
          let uu____14990 =
            let uu____14991 =
              let uu____15002 =
                let uu____15003 =
                  let uu____15008 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____15008)  in
                FStar_SMTEncoding_Util.mkImp uu____15003  in
              ([[typing_pred]], [xx], uu____15002)  in
            mkForall_fuel uu____14991  in
          (uu____14990, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14983  in
      [uu____14982]  in
    uu____14968 :: uu____14979  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15050 =
      let uu____15051 =
        let uu____15058 =
          let uu____15059 =
            let uu____15070 =
              let uu____15075 =
                let uu____15078 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____15078]  in
              [uu____15075]  in
            let uu____15083 =
              let uu____15084 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15084 tt  in
            (uu____15070, [bb], uu____15083)  in
          FStar_SMTEncoding_Util.mkForall uu____15059  in
        (uu____15058, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15051  in
    let uu____15105 =
      let uu____15108 =
        let uu____15109 =
          let uu____15116 =
            let uu____15117 =
              let uu____15128 =
                let uu____15129 =
                  let uu____15134 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____15134)  in
                FStar_SMTEncoding_Util.mkImp uu____15129  in
              ([[typing_pred]], [xx], uu____15128)  in
            mkForall_fuel uu____15117  in
          (uu____15116, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15109  in
      [uu____15108]  in
    uu____15050 :: uu____15105  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____15184 =
        let uu____15185 =
          let uu____15192 =
            let uu____15195 =
              let uu____15198 =
                let uu____15201 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____15202 =
                  let uu____15205 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____15205]  in
                uu____15201 :: uu____15202  in
              tt :: uu____15198  in
            tt :: uu____15195  in
          ("Prims.Precedes", uu____15192)  in
        FStar_SMTEncoding_Util.mkApp uu____15185  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15184  in
    let precedes_y_x =
      let uu____15209 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____15209  in
    let uu____15212 =
      let uu____15213 =
        let uu____15220 =
          let uu____15221 =
            let uu____15232 =
              let uu____15237 =
                let uu____15240 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____15240]  in
              [uu____15237]  in
            let uu____15245 =
              let uu____15246 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15246 tt  in
            (uu____15232, [bb], uu____15245)  in
          FStar_SMTEncoding_Util.mkForall uu____15221  in
        (uu____15220, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15213  in
    let uu____15267 =
      let uu____15270 =
        let uu____15271 =
          let uu____15278 =
            let uu____15279 =
              let uu____15290 =
                let uu____15291 =
                  let uu____15296 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15296)  in
                FStar_SMTEncoding_Util.mkImp uu____15291  in
              ([[typing_pred]], [xx], uu____15290)  in
            mkForall_fuel uu____15279  in
          (uu____15278, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15271  in
      let uu____15321 =
        let uu____15324 =
          let uu____15325 =
            let uu____15332 =
              let uu____15333 =
                let uu____15344 =
                  let uu____15345 =
                    let uu____15350 =
                      let uu____15351 =
                        let uu____15354 =
                          let uu____15357 =
                            let uu____15360 =
                              let uu____15361 =
                                let uu____15366 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15367 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15366, uu____15367)  in
                              FStar_SMTEncoding_Util.mkGT uu____15361  in
                            let uu____15368 =
                              let uu____15371 =
                                let uu____15372 =
                                  let uu____15377 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15378 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15377, uu____15378)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15372  in
                              let uu____15379 =
                                let uu____15382 =
                                  let uu____15383 =
                                    let uu____15388 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15389 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15388, uu____15389)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15383  in
                                [uu____15382]  in
                              uu____15371 :: uu____15379  in
                            uu____15360 :: uu____15368  in
                          typing_pred_y :: uu____15357  in
                        typing_pred :: uu____15354  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15351  in
                    (uu____15350, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15345  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15344)
                 in
              mkForall_fuel uu____15333  in
            (uu____15332,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15325  in
        [uu____15324]  in
      uu____15270 :: uu____15321  in
    uu____15212 :: uu____15267  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15435 =
      let uu____15436 =
        let uu____15443 =
          let uu____15444 =
            let uu____15455 =
              let uu____15460 =
                let uu____15463 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15463]  in
              [uu____15460]  in
            let uu____15468 =
              let uu____15469 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15469 tt  in
            (uu____15455, [bb], uu____15468)  in
          FStar_SMTEncoding_Util.mkForall uu____15444  in
        (uu____15443, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15436  in
    let uu____15490 =
      let uu____15493 =
        let uu____15494 =
          let uu____15501 =
            let uu____15502 =
              let uu____15513 =
                let uu____15514 =
                  let uu____15519 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15519)  in
                FStar_SMTEncoding_Util.mkImp uu____15514  in
              ([[typing_pred]], [xx], uu____15513)  in
            mkForall_fuel uu____15502  in
          (uu____15501, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15494  in
      [uu____15493]  in
    uu____15435 :: uu____15490  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15572 =
      let uu____15573 =
        let uu____15580 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15580, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15573  in
    [uu____15572]  in
  let mk_and_interp env conj uu____15592 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15617 =
      let uu____15618 =
        let uu____15625 =
          let uu____15626 =
            let uu____15637 =
              let uu____15638 =
                let uu____15643 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15643, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15638  in
            ([[l_and_a_b]], [aa; bb], uu____15637)  in
          FStar_SMTEncoding_Util.mkForall uu____15626  in
        (uu____15625, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15618  in
    [uu____15617]  in
  let mk_or_interp env disj uu____15681 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15706 =
      let uu____15707 =
        let uu____15714 =
          let uu____15715 =
            let uu____15726 =
              let uu____15727 =
                let uu____15732 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15732, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15727  in
            ([[l_or_a_b]], [aa; bb], uu____15726)  in
          FStar_SMTEncoding_Util.mkForall uu____15715  in
        (uu____15714, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15707  in
    [uu____15706]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15795 =
      let uu____15796 =
        let uu____15803 =
          let uu____15804 =
            let uu____15815 =
              let uu____15816 =
                let uu____15821 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15821, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15816  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15815)  in
          FStar_SMTEncoding_Util.mkForall uu____15804  in
        (uu____15803, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15796  in
    [uu____15795]  in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y])  in
    let uu____15894 =
      let uu____15895 =
        let uu____15902 =
          let uu____15903 =
            let uu____15914 =
              let uu____15915 =
                let uu____15920 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15920, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15915  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15914)  in
          FStar_SMTEncoding_Util.mkForall uu____15903  in
        (uu____15902, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15895  in
    [uu____15894]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15991 =
      let uu____15992 =
        let uu____15999 =
          let uu____16000 =
            let uu____16011 =
              let uu____16012 =
                let uu____16017 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____16017, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16012  in
            ([[l_imp_a_b]], [aa; bb], uu____16011)  in
          FStar_SMTEncoding_Util.mkForall uu____16000  in
        (uu____15999, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15992  in
    [uu____15991]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____16080 =
      let uu____16081 =
        let uu____16088 =
          let uu____16089 =
            let uu____16100 =
              let uu____16101 =
                let uu____16106 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____16106, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16101  in
            ([[l_iff_a_b]], [aa; bb], uu____16100)  in
          FStar_SMTEncoding_Util.mkForall uu____16089  in
        (uu____16088, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16081  in
    [uu____16080]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____16158 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____16158  in
    let uu____16161 =
      let uu____16162 =
        let uu____16169 =
          let uu____16170 =
            let uu____16181 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____16181)  in
          FStar_SMTEncoding_Util.mkForall uu____16170  in
        (uu____16169, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16162  in
    [uu____16161]  in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b])  in
    let valid_b_x =
      let uu____16241 =
        let uu____16248 =
          let uu____16251 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16251]  in
        ("Valid", uu____16248)  in
      FStar_SMTEncoding_Util.mkApp uu____16241  in
    let uu____16254 =
      let uu____16255 =
        let uu____16262 =
          let uu____16263 =
            let uu____16274 =
              let uu____16275 =
                let uu____16280 =
                  let uu____16281 =
                    let uu____16292 =
                      let uu____16297 =
                        let uu____16300 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16300]  in
                      [uu____16297]  in
                    let uu____16305 =
                      let uu____16306 =
                        let uu____16311 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16311, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16306  in
                    (uu____16292, [xx1], uu____16305)  in
                  FStar_SMTEncoding_Util.mkForall uu____16281  in
                (uu____16280, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16275  in
            ([[l_forall_a_b]], [aa; bb], uu____16274)  in
          FStar_SMTEncoding_Util.mkForall uu____16263  in
        (uu____16262, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16255  in
    [uu____16254]  in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b])  in
    let valid_b_x =
      let uu____16393 =
        let uu____16400 =
          let uu____16403 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16403]  in
        ("Valid", uu____16400)  in
      FStar_SMTEncoding_Util.mkApp uu____16393  in
    let uu____16406 =
      let uu____16407 =
        let uu____16414 =
          let uu____16415 =
            let uu____16426 =
              let uu____16427 =
                let uu____16432 =
                  let uu____16433 =
                    let uu____16444 =
                      let uu____16449 =
                        let uu____16452 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16452]  in
                      [uu____16449]  in
                    let uu____16457 =
                      let uu____16458 =
                        let uu____16463 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16463, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16458  in
                    (uu____16444, [xx1], uu____16457)  in
                  FStar_SMTEncoding_Util.mkExists uu____16433  in
                (uu____16432, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16427  in
            ([[l_exists_a_b]], [aa; bb], uu____16426)  in
          FStar_SMTEncoding_Util.mkForall uu____16415  in
        (uu____16414, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16407  in
    [uu____16406]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16523 =
      let uu____16524 =
        let uu____16531 =
          let uu____16532 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16532 range_ty  in
        let uu____16533 = varops.mk_unique "typing_range_const"  in
        (uu____16531, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16533)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16524  in
    [uu____16523]  in
  let mk_inversion_axiom env inversion tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let inversion_t = FStar_SMTEncoding_Util.mkApp (inversion, [t])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [inversion_t])  in
    let body =
      let hastypeZ = FStar_SMTEncoding_Term.mk_HasTypeZ x1 t  in
      let hastypeS =
        let uu____16567 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16567 x1 t  in
      let uu____16568 =
        let uu____16579 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16579)  in
      FStar_SMTEncoding_Util.mkForall uu____16568  in
    let uu____16602 =
      let uu____16603 =
        let uu____16610 =
          let uu____16611 =
            let uu____16622 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16622)  in
          FStar_SMTEncoding_Util.mkForall uu____16611  in
        (uu____16610,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16603  in
    [uu____16602]  in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.true_lid, mk_true_interp);
    (FStar_Parser_Const.false_lid, mk_false_interp);
    (FStar_Parser_Const.and_lid, mk_and_interp);
    (FStar_Parser_Const.or_lid, mk_or_interp);
    (FStar_Parser_Const.eq2_lid, mk_eq2_interp);
    (FStar_Parser_Const.eq3_lid, mk_eq3_interp);
    (FStar_Parser_Const.imp_lid, mk_imp_interp);
    (FStar_Parser_Const.iff_lid, mk_iff_interp);
    (FStar_Parser_Const.not_lid, mk_not_interp);
    (FStar_Parser_Const.forall_lid, mk_forall_interp);
    (FStar_Parser_Const.exists_lid, mk_exists_interp);
    (FStar_Parser_Const.range_lid, mk_range_interp);
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16946 =
            FStar_Util.find_opt
              (fun uu____16972  ->
                 match uu____16972 with
                 | (l,uu____16984) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16946 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____17009,f) -> f env s tt
  
let encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____17045 = encode_function_type_as_formula t env  in
        match uu____17045 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let encode_free_var :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____17085 =
                ((let uu____17088 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____17088) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____17085
              then
                let uu____17095 = new_term_constant_and_tok_from_lid env lid
                   in
                match uu____17095 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____17114 =
                        let uu____17115 = FStar_Syntax_Subst.compress t_norm
                           in
                        uu____17115.FStar_Syntax_Syntax.n  in
                      match uu____17114 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____17121) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17151  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17156 -> []  in
                    let d =
                      FStar_SMTEncoding_Term.DeclFun
                        (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted function symbol for impure function"))
                       in
                    let dd =
                      FStar_SMTEncoding_Term.DeclFun
                        (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                          (FStar_Pervasives_Native.Some
                             "Uninterpreted name for impure function"))
                       in
                    ([d; dd], env1)
              else
                (let uu____17170 = prims.is lid  in
                 if uu____17170
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17178 = prims.mk lid vname  in
                   match uu____17178 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17202 =
                      let uu____17213 = curried_arrow_formals_comp t_norm  in
                      match uu____17213 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17231 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17231
                            then
                              let uu____17232 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___350_17235 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___350_17235.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___350_17235.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___350_17235.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___350_17235.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___350_17235.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___350_17235.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___350_17235.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___350_17235.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___350_17235.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___350_17235.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___350_17235.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___350_17235.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___350_17235.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___350_17235.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___350_17235.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___350_17235.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___350_17235.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___350_17235.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___350_17235.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___350_17235.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___350_17235.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___350_17235.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___350_17235.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___350_17235.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___350_17235.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___350_17235.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___350_17235.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___350_17235.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___350_17235.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___350_17235.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___350_17235.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___350_17235.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___350_17235.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17232
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17247 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17247)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17202 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17292 =
                          new_term_constant_and_tok_from_lid env lid  in
                        (match uu____17292 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17313 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___322_17355  ->
                                       match uu___322_17355 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17359 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17359 with
                                            | (uu____17380,(xxsym,uu____17382))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17400 =
                                                  let uu____17401 =
                                                    let uu____17408 =
                                                      let uu____17409 =
                                                        let uu____17420 =
                                                          let uu____17421 =
                                                            let uu____17426 =
                                                              let uu____17427
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17427
                                                               in
                                                            (vapp,
                                                              uu____17426)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17421
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17420)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17409
                                                       in
                                                    (uu____17408,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17401
                                                   in
                                                [uu____17400])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17446 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17446 with
                                            | (uu____17467,(xxsym,uu____17469))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let f1 =
                                                  {
                                                    FStar_Syntax_Syntax.ppname
                                                      = f;
                                                    FStar_Syntax_Syntax.index
                                                      = (Prims.parse_int "0");
                                                    FStar_Syntax_Syntax.sort
                                                      =
                                                      FStar_Syntax_Syntax.tun
                                                  }  in
                                                let tp_name =
                                                  mk_term_projector_name d f1
                                                   in
                                                let prim_app =
                                                  FStar_SMTEncoding_Util.mkApp
                                                    (tp_name, [xx])
                                                   in
                                                let uu____17492 =
                                                  let uu____17493 =
                                                    let uu____17500 =
                                                      let uu____17501 =
                                                        let uu____17512 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17512)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17501
                                                       in
                                                    (uu____17500,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17493
                                                   in
                                                [uu____17492])
                                       | uu____17529 -> []))
                                in
                             let uu____17530 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17530 with
                              | (vars,guards,env',decls1,uu____17557) ->
                                  let uu____17570 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17579 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17579, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17581 =
                                          encode_formula p env'  in
                                        (match uu____17581 with
                                         | (g,ds) ->
                                             let uu____17592 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17592,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17570 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17605 =
                                           let uu____17612 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17612)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17605
                                          in
                                       let uu____17621 =
                                         let vname_decl =
                                           let uu____17629 =
                                             let uu____17640 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17650  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17640,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17629
                                            in
                                         let uu____17659 =
                                           let env2 =
                                             let uu___351_17665 = env1  in
                                             {
                                               bindings =
                                                 (uu___351_17665.bindings);
                                               depth = (uu___351_17665.depth);
                                               tcenv = (uu___351_17665.tcenv);
                                               warn = (uu___351_17665.warn);
                                               cache = (uu___351_17665.cache);
                                               nolabels =
                                                 (uu___351_17665.nolabels);
                                               use_zfuel_name =
                                                 (uu___351_17665.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___351_17665.current_module_name)
                                             }  in
                                           let uu____17666 =
                                             let uu____17667 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17667
                                              in
                                           if uu____17666
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17659 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17682::uu____17683 ->
                                                   let ff =
                                                     ("ty",
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                      in
                                                   let f =
                                                     FStar_SMTEncoding_Util.mkFreeV
                                                       ff
                                                      in
                                                   let vtok_app_l =
                                                     mk_Apply vtok_tm [ff]
                                                      in
                                                   let vtok_app_r =
                                                     mk_Apply f
                                                       [(vtok,
                                                          FStar_SMTEncoding_Term.Term_sort)]
                                                      in
                                                   let guarded_tok_typing =
                                                     let uu____17723 =
                                                       let uu____17734 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17734)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17723
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17761 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17764 =
                                               match formals with
                                               | [] ->
                                                   let uu____17781 =
                                                     let uu____17782 =
                                                       let uu____17785 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17785
                                                        in
                                                     push_free_var env1 lid
                                                       vname uu____17782
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17781)
                                               | uu____17790 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17797 =
                                                       let uu____17804 =
                                                         let uu____17805 =
                                                           let uu____17816 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17816)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17805
                                                          in
                                                       (uu____17804,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17797
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17764 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17621 with
                                        | (decls2,env2) ->
                                            let uu____17859 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17867 =
                                                encode_term res_t1 env'  in
                                              match uu____17867 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17880 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17880, decls)
                                               in
                                            (match uu____17859 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17891 =
                                                     let uu____17898 =
                                                       let uu____17899 =
                                                         let uu____17910 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17910)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17899
                                                        in
                                                     (uu____17898,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17891
                                                    in
                                                 let freshness =
                                                   let uu____17926 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17926
                                                   then
                                                     let uu____17931 =
                                                       let uu____17932 =
                                                         let uu____17943 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17954 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17943,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17954)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17932
                                                        in
                                                     let uu____17957 =
                                                       let uu____17960 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17960]  in
                                                     uu____17931 ::
                                                       uu____17957
                                                   else []  in
                                                 let g =
                                                   let uu____17965 =
                                                     let uu____17968 =
                                                       let uu____17971 =
                                                         let uu____17974 =
                                                           let uu____17977 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____17977
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17974
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____17971
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17968
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17965
                                                    in
                                                 (g, env2))))))))
  
let declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____18008 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____18008 with
          | FStar_Pervasives_Native.None  ->
              let uu____18045 = encode_free_var false env x t t_norm []  in
              (match uu____18045 with
               | (decls,env1) ->
                   let uu____18072 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____18072 with
                    | (n1,x',uu____18099) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____18120) ->
              ((n1, x1), [], env)
  
let encode_top_level_val :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t  in
            let uu____18175 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____18175 with
            | (decls,env1) ->
                let uu____18194 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18194
                then
                  let uu____18201 =
                    let uu____18204 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18204  in
                  (uu____18201, env1)
                else (decls, env1)
  
let encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18256  ->
                fun lb  ->
                  match uu____18256 with
                  | (decls,env1) ->
                      let uu____18276 =
                        let uu____18283 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18283
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18276 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let is_tactic : FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18304 = FStar_Syntax_Util.head_and_args t  in
    match uu____18304 with
    | (hd1,args) ->
        let uu____18341 =
          let uu____18342 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18342.FStar_Syntax_Syntax.n  in
        (match uu____18341 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18346,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18365 -> false)
  
let encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____18387  ->
      fun quals  ->
        match uu____18387 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18463 = FStar_Util.first_N nbinders formals  in
              match uu____18463 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18544  ->
                         fun uu____18545  ->
                           match (uu____18544, uu____18545) with
                           | ((formal,uu____18563),(binder,uu____18565)) ->
                               let uu____18574 =
                                 let uu____18581 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18581)  in
                               FStar_Syntax_Syntax.NT uu____18574) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18589 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18620  ->
                              match uu____18620 with
                              | (x,i) ->
                                  let uu____18631 =
                                    let uu___352_18632 = x  in
                                    let uu____18633 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___352_18632.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___352_18632.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18633
                                    }  in
                                  (uu____18631, i)))
                       in
                    FStar_All.pipe_right uu____18589
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18651 =
                      let uu____18652 = FStar_Syntax_Subst.compress body  in
                      let uu____18653 =
                        let uu____18654 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18654
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18652
                        uu____18653
                       in
                    uu____18651 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18715 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18715
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___353_18718 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___353_18718.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___353_18718.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___353_18718.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___353_18718.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___353_18718.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___353_18718.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___353_18718.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___353_18718.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___353_18718.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___353_18718.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___353_18718.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___353_18718.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___353_18718.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___353_18718.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___353_18718.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___353_18718.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___353_18718.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___353_18718.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___353_18718.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___353_18718.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___353_18718.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___353_18718.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___353_18718.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___353_18718.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___353_18718.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___353_18718.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___353_18718.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___353_18718.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___353_18718.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___353_18718.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___353_18718.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___353_18718.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___353_18718.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18751 = FStar_Syntax_Util.abs_formals e  in
                match uu____18751 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18815::uu____18816 ->
                         let uu____18831 =
                           let uu____18832 =
                             let uu____18835 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18835
                              in
                           uu____18832.FStar_Syntax_Syntax.n  in
                         (match uu____18831 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18878 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18878 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18920 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18920
                                   then
                                     let uu____18955 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____18955 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____19049  ->
                                                   fun uu____19050  ->
                                                     match (uu____19049,
                                                             uu____19050)
                                                     with
                                                     | ((x,uu____19068),
                                                        (b,uu____19070)) ->
                                                         let uu____19079 =
                                                           let uu____19086 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____19086)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____19079)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____19088 =
                                            let uu____19109 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____19109)
                                             in
                                          (uu____19088, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19177 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____19177 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19266) ->
                              let uu____19271 =
                                let uu____19292 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19292  in
                              (uu____19271, true)
                          | uu____19357 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.Weak;
                                  FStar_TypeChecker_Normalize.HNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1
                                 in
                              aux true t_norm2
                          | uu____19359 ->
                              let uu____19360 =
                                let uu____19361 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19362 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19361
                                  uu____19362
                                 in
                              failwith uu____19360)
                     | uu____19387 ->
                         let rec aux' t_norm2 =
                           let uu____19412 =
                             let uu____19413 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19413.FStar_Syntax_Syntax.n  in
                           match uu____19412 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19454 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19454 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19482 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19482 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19562)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19567 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____19623 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19623
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19635 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19729  ->
                            fun lb  ->
                              match uu____19729 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19824 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19824
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19827 =
                                      let uu____19842 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19842
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19827 with
                                    | (tok,decl,env2) ->
                                        let uu____19888 =
                                          let uu____19901 =
                                            let uu____19912 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____19912, tok)  in
                                          uu____19901 :: toks  in
                                        (uu____19888, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19635 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks  in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten
                         in
                      let typs1 = FStar_List.rev typs  in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____20095 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____20103 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____20103 vars)
                            else
                              (let uu____20105 =
                                 let uu____20112 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____20112)  in
                               FStar_SMTEncoding_Util.mkApp uu____20105)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20194;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20196;
                             FStar_Syntax_Syntax.lbeff = uu____20197;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            let uu____20260 =
                              let uu____20267 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____20267 with
                              | (tcenv',uu____20285,e_t) ->
                                  let uu____20291 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20302 -> failwith "Impossible"
                                     in
                                  (match uu____20291 with
                                   | (e1,t_norm1) ->
                                       ((let uu___356_20318 = env2  in
                                         {
                                           bindings =
                                             (uu___356_20318.bindings);
                                           depth = (uu___356_20318.depth);
                                           tcenv = tcenv';
                                           warn = (uu___356_20318.warn);
                                           cache = (uu___356_20318.cache);
                                           nolabels =
                                             (uu___356_20318.nolabels);
                                           use_zfuel_name =
                                             (uu___356_20318.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___356_20318.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___356_20318.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____20260 with
                             | (env',e1,t_norm1) ->
                                 let uu____20328 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____20328 with
                                  | ((binders,body,uu____20349,uu____20350),curry)
                                      ->
                                      ((let uu____20361 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____20361
                                        then
                                          let uu____20362 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____20363 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20362 uu____20363
                                        else ());
                                       (let uu____20365 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____20365 with
                                        | (vars,guards,env'1,binder_decls,uu____20392)
                                            ->
                                            let body1 =
                                              let uu____20406 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____20406
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body  in
                                            let app =
                                              mk_app1 curry f ftok vars  in
                                            let uu____20409 =
                                              let uu____20418 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____20418
                                              then
                                                let uu____20429 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____20430 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____20429, uu____20430)
                                              else
                                                (let uu____20440 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____20440))
                                               in
                                            (match uu____20409 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20463 =
                                                     let uu____20470 =
                                                       let uu____20471 =
                                                         let uu____20482 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____20482)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20471
                                                        in
                                                     let uu____20493 =
                                                       let uu____20496 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20496
                                                        in
                                                     (uu____20470,
                                                       uu____20493,
                                                       (Prims.strcat
                                                          "equation_" f))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20463
                                                    in
                                                 let uu____20499 =
                                                   let uu____20502 =
                                                     let uu____20505 =
                                                       let uu____20508 =
                                                         let uu____20511 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____20511
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____20508
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20505
                                                      in
                                                   FStar_List.append decls1
                                                     uu____20502
                                                    in
                                                 (uu____20499, env2))))))
                        | uu____20516 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20601 = varops.fresh "fuel"  in
                          (uu____20601, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____20604 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20692  ->
                                  fun uu____20693  ->
                                    match (uu____20692, uu____20693) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                           in
                                        let g =
                                          let uu____20841 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____20841  in
                                        let gtok =
                                          let uu____20843 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____20843  in
                                        let env4 =
                                          let uu____20845 =
                                            let uu____20848 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20848
                                             in
                                          push_free_var env3 flid gtok
                                            uu____20845
                                           in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2))
                           in
                        match uu____20604 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____21004 t_norm
                              uu____21006 =
                              match (uu____21004, uu____21006) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____21050;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____21051;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____21079 =
                                    let uu____21086 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____21086 with
                                    | (tcenv',uu____21108,e_t) ->
                                        let uu____21114 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____21125 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____21114 with
                                         | (e1,t_norm1) ->
                                             ((let uu___357_21141 = env3  in
                                               {
                                                 bindings =
                                                   (uu___357_21141.bindings);
                                                 depth =
                                                   (uu___357_21141.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___357_21141.warn);
                                                 cache =
                                                   (uu___357_21141.cache);
                                                 nolabels =
                                                   (uu___357_21141.nolabels);
                                                 use_zfuel_name =
                                                   (uu___357_21141.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___357_21141.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___357_21141.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____21079 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21156 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____21156
                                         then
                                           let uu____21157 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____21158 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____21159 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21157 uu____21158
                                             uu____21159
                                         else ());
                                        (let uu____21161 =
                                           destruct_bound_function flid
                                             t_norm1 e1
                                            in
                                         match uu____21161 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21198 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____21198
                                               then
                                                 let uu____21199 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____21200 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____21201 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____21202 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21199 uu____21200
                                                   uu____21201 uu____21202
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21206 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____21206 with
                                               | (vars,guards,env'1,binder_decls,uu____21237)
                                                   ->
                                                   let decl_g =
                                                     let uu____21251 =
                                                       let uu____21262 =
                                                         let uu____21265 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21265
                                                          in
                                                       (g, uu____21262,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21251
                                                      in
                                                   let env02 =
                                                     push_zfuel_name env01
                                                       flid g
                                                      in
                                                   let decl_g_tok =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (gtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Token for fuel-instrumented partial applications"))
                                                      in
                                                   let vars_tm =
                                                     FStar_List.map
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                       vars
                                                      in
                                                   let app =
                                                     let uu____21290 =
                                                       let uu____21297 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       (f, uu____21297)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21290
                                                      in
                                                   let gsapp =
                                                     let uu____21307 =
                                                       let uu____21314 =
                                                         let uu____21317 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____21317 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21314)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21307
                                                      in
                                                   let gmax =
                                                     let uu____21323 =
                                                       let uu____21330 =
                                                         let uu____21333 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____21333 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21330)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21323
                                                      in
                                                   let body1 =
                                                     let uu____21339 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____21339
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____21341 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____21341 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21359 =
                                                            let uu____21366 =
                                                              let uu____21367
                                                                =
                                                                let uu____21382
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm)
                                                                   in
                                                                ([[gsapp]],
                                                                  (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int "0")),
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21382)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21367
                                                               in
                                                            let uu____21403 =
                                                              let uu____21406
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21406
                                                               in
                                                            (uu____21366,
                                                              uu____21403,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21359
                                                           in
                                                        let eqn_f =
                                                          let uu____21410 =
                                                            let uu____21417 =
                                                              let uu____21418
                                                                =
                                                                let uu____21429
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21429)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21418
                                                               in
                                                            (uu____21417,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21410
                                                           in
                                                        let eqn_g' =
                                                          let uu____21443 =
                                                            let uu____21450 =
                                                              let uu____21451
                                                                =
                                                                let uu____21462
                                                                  =
                                                                  let uu____21463
                                                                    =
                                                                    let uu____21468
                                                                    =
                                                                    let uu____21469
                                                                    =
                                                                    let uu____21476
                                                                    =
                                                                    let uu____21479
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____21479
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____21476)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21469
                                                                     in
                                                                    (gsapp,
                                                                    uu____21468)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21463
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21462)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21451
                                                               in
                                                            (uu____21450,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21443
                                                           in
                                                        let uu____21502 =
                                                          let uu____21511 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____21511
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21540)
                                                              ->
                                                              let vars_tm1 =
                                                                FStar_List.map
                                                                  FStar_SMTEncoding_Util.mkFreeV
                                                                  vars1
                                                                 in
                                                              let gapp =
                                                                FStar_SMTEncoding_Util.mkApp
                                                                  (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1))
                                                                 in
                                                              let tok_corr =
                                                                let tok_app =
                                                                  let uu____21565
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____21565
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____21570
                                                                  =
                                                                  let uu____21577
                                                                    =
                                                                    let uu____21578
                                                                    =
                                                                    let uu____21589
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21589)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21578
                                                                     in
                                                                  (uu____21577,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21570
                                                                 in
                                                              let uu____21610
                                                                =
                                                                let uu____21617
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____21617
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21630
                                                                    =
                                                                    let uu____21633
                                                                    =
                                                                    let uu____21634
                                                                    =
                                                                    let uu____21641
                                                                    =
                                                                    let uu____21642
                                                                    =
                                                                    let uu____21653
                                                                    =
                                                                    let uu____21654
                                                                    =
                                                                    let uu____21659
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____21659,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21654
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21653)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21642
                                                                     in
                                                                    (uu____21641,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21634
                                                                     in
                                                                    [uu____21633]
                                                                     in
                                                                    (d3,
                                                                    uu____21630)
                                                                 in
                                                              (match uu____21610
                                                               with
                                                               | (aux_decls,typing_corr)
                                                                   ->
                                                                   ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr])))
                                                           in
                                                        (match uu____21502
                                                         with
                                                         | (aux_decls,g_typing)
                                                             ->
                                                             ((FStar_List.append
                                                                 binder_decls
                                                                 (FStar_List.append
                                                                    decls2
                                                                    (
                                                                    FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                               (FStar_List.append
                                                                  [eqn_g;
                                                                  eqn_g';
                                                                  eqn_f]
                                                                  g_typing),
                                                               env02))))))))
                               in
                            let uu____21724 =
                              let uu____21737 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____21816  ->
                                   fun uu____21817  ->
                                     match (uu____21816, uu____21817) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21972 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____21972 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21737
                               in
                            (match uu____21724 with
                             | (decls2,eqns,env01) ->
                                 let uu____22045 =
                                   let isDeclFun uu___323_22057 =
                                     match uu___323_22057 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____22058 -> true
                                     | uu____22069 -> false  in
                                   let uu____22070 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____22070
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____22045 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____22110 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___324_22114  ->
                                 match uu___324_22114 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____22115 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____22121 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____22121)))
                         in
                      if uu____22110
                      then (decls1, env1)
                      else
                        (try
                           if Prims.op_Negation is_rec
                           then
                             encode_non_rec_lbdef bindings typs1 toks1 env1
                           else encode_rec_lbdefs bindings typs1 toks1 env1
                         with | Inner_let_rec  -> (decls1, env1)))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____22173 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22173
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____22222 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22222 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22226 = encode_sigelt' env se  in
      match uu____22226 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22242 =
                  let uu____22243 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22243  in
                [uu____22242]
            | uu____22244 ->
                let uu____22245 =
                  let uu____22248 =
                    let uu____22249 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22249  in
                  uu____22248 :: g  in
                let uu____22250 =
                  let uu____22253 =
                    let uu____22254 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22254  in
                  [uu____22253]  in
                FStar_List.append uu____22245 uu____22250
             in
          (g1, env1)

and encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22267 =
          let uu____22268 = FStar_Syntax_Subst.compress t  in
          uu____22268.FStar_Syntax_Syntax.n  in
        match uu____22267 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22272)) -> s = "opaque_to_smt"
        | uu____22273 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22278 =
          let uu____22279 = FStar_Syntax_Subst.compress t  in
          uu____22279.FStar_Syntax_Syntax.n  in
        match uu____22278 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22283)) -> s = "uninterpreted_by_smt"
        | uu____22284 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22289 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22294 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22297 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22300 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22315 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22319 =
            let uu____22320 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____22320 Prims.op_Negation  in
          if uu____22319
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22346 ->
                   FStar_Syntax_Syntax.mk
                     (FStar_Syntax_Syntax.Tm_abs
                        ((ed.FStar_Syntax_Syntax.binders), tm,
                          (FStar_Pervasives_Native.Some
                             (FStar_Syntax_Util.mk_residual_comp
                                FStar_Parser_Const.effect_Tot_lid
                                FStar_Pervasives_Native.None
                                [FStar_Syntax_Syntax.TOTAL]))))
                     FStar_Pervasives_Native.None tm.FStar_Syntax_Syntax.pos
                in
             let encode_action env1 a =
               let uu____22366 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____22366 with
               | (aname,atok,env2) ->
                   let uu____22382 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____22382 with
                    | (formals,uu____22400) ->
                        let uu____22413 =
                          let uu____22418 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____22418 env2  in
                        (match uu____22413 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22430 =
                                 let uu____22431 =
                                   let uu____22442 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22458  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____22442,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____22431
                                  in
                               [uu____22430;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____22471 =
                               let aux uu____22523 uu____22524 =
                                 match (uu____22523, uu____22524) with
                                 | ((bv,uu____22576),(env3,acc_sorts,acc)) ->
                                     let uu____22614 = gen_term_var env3 bv
                                        in
                                     (match uu____22614 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____22471 with
                              | (uu____22686,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____22709 =
                                      let uu____22716 =
                                        let uu____22717 =
                                          let uu____22728 =
                                            let uu____22729 =
                                              let uu____22734 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____22734)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22729
                                             in
                                          ([[app]], xs_sorts, uu____22728)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22717
                                         in
                                      (uu____22716,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22709
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____22754 =
                                      let uu____22761 =
                                        let uu____22762 =
                                          let uu____22773 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____22773)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22762
                                         in
                                      (uu____22761,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22754
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____22792 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____22792 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22820,uu____22821)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22822 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____22822 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22839,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____22845 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___325_22849  ->
                      match uu___325_22849 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22850 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22855 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22856 -> false))
               in
            Prims.op_Negation uu____22845  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____22865 =
               let uu____22872 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____22872 env fv t quals  in
             match uu____22865 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____22887 =
                   let uu____22890 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____22890  in
                 (uu____22887, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22898 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____22898 with
           | (uu____22907,f1) ->
               let uu____22909 = encode_formula f1 env  in
               (match uu____22909 with
                | (f2,decls) ->
                    let g =
                      let uu____22923 =
                        let uu____22924 =
                          let uu____22931 =
                            let uu____22934 =
                              let uu____22935 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____22935
                               in
                            FStar_Pervasives_Native.Some uu____22934  in
                          let uu____22936 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____22931, uu____22936)  in
                        FStar_SMTEncoding_Util.mkAssume uu____22924  in
                      [uu____22923]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22942) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____22954 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22972 =
                       let uu____22975 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____22975.FStar_Syntax_Syntax.fv_name  in
                     uu____22972.FStar_Syntax_Syntax.v  in
                   let uu____22976 =
                     let uu____22977 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____22977  in
                   if uu____22976
                   then
                     let val_decl =
                       let uu___360_23005 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___360_23005.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___360_23005.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___360_23005.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____23010 = encode_sigelt' env1 val_decl  in
                     match uu____23010 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____22954 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____23038,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____23040;
                          FStar_Syntax_Syntax.lbtyp = uu____23041;
                          FStar_Syntax_Syntax.lbeff = uu____23042;
                          FStar_Syntax_Syntax.lbdef = uu____23043;_}::[]),uu____23044)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____23063 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____23063 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____23092 =
                   let uu____23095 =
                     let uu____23096 =
                       let uu____23103 =
                         let uu____23104 =
                           let uu____23115 =
                             let uu____23116 =
                               let uu____23121 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____23121)  in
                             FStar_SMTEncoding_Util.mkEq uu____23116  in
                           ([[b2t_x]], [xx], uu____23115)  in
                         FStar_SMTEncoding_Util.mkForall uu____23104  in
                       (uu____23103,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____23096  in
                   [uu____23095]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____23092
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23154,uu____23155) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___326_23164  ->
                  match uu___326_23164 with
                  | FStar_Syntax_Syntax.Discriminator uu____23165 -> true
                  | uu____23166 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23169,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23180 =
                     let uu____23181 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23181.FStar_Ident.idText  in
                   uu____23180 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___327_23185  ->
                     match uu___327_23185 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23186 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23190) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___328_23207  ->
                  match uu___328_23207 with
                  | FStar_Syntax_Syntax.Projector uu____23208 -> true
                  | uu____23213 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23216 = try_lookup_free_var env l  in
          (match uu____23216 with
           | FStar_Pervasives_Native.Some uu____23223 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___361_23227 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___361_23227.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___361_23227.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___361_23227.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23234) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23252) ->
          let uu____23261 = encode_sigelts env ses  in
          (match uu____23261 with
           | (g,env1) ->
               let uu____23278 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___329_23301  ->
                         match uu___329_23301 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23302;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23303;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23304;_}
                             -> false
                         | uu____23307 -> true))
                  in
               (match uu____23278 with
                | (g',inversions) ->
                    let uu____23322 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___330_23343  ->
                              match uu___330_23343 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23344 ->
                                  true
                              | uu____23355 -> false))
                       in
                    (match uu____23322 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23373,tps,k,uu____23376,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___331_23393  ->
                    match uu___331_23393 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23394 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23403 = c  in
              match uu____23403 with
              | (name,args,uu____23408,uu____23409,uu____23410) ->
                  let uu____23415 =
                    let uu____23416 =
                      let uu____23427 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23444  ->
                                match uu____23444 with
                                | (uu____23451,sort,uu____23453) -> sort))
                         in
                      (name, uu____23427, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____23416  in
                  [uu____23415]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____23480 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23486 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____23486 FStar_Option.isNone))
               in
            if uu____23480
            then []
            else
              (let uu____23518 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____23518 with
               | (xxsym,xx) ->
                   let uu____23527 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23566  ->
                             fun l  ->
                               match uu____23566 with
                               | (out,decls) ->
                                   let uu____23586 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____23586 with
                                    | (uu____23597,data_t) ->
                                        let uu____23599 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____23599 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23645 =
                                                 let uu____23646 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____23646.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____23645 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23657,indices) ->
                                                   indices
                                               | uu____23679 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23703  ->
                                                         match uu____23703
                                                         with
                                                         | (x,uu____23709) ->
                                                             let uu____23710
                                                               =
                                                               let uu____23711
                                                                 =
                                                                 let uu____23718
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____23718,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23711
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____23710)
                                                    env)
                                                in
                                             let uu____23721 =
                                               encode_args indices env1  in
                                             (match uu____23721 with
                                              | (indices1,decls') ->
                                                  (if
                                                     (FStar_List.length
                                                        indices1)
                                                       <>
                                                       (FStar_List.length
                                                          vars)
                                                   then failwith "Impossible"
                                                   else ();
                                                   (let eqs =
                                                      let uu____23747 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23763
                                                                 =
                                                                 let uu____23768
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23768,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23763)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23747
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23771 =
                                                      let uu____23772 =
                                                        let uu____23777 =
                                                          let uu____23778 =
                                                            let uu____23783 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23783,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23778
                                                           in
                                                        (out, uu____23777)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23772
                                                       in
                                                    (uu____23771,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____23527 with
                    | (data_ax,decls) ->
                        let uu____23796 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23796 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23807 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23807 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23811 =
                                 let uu____23818 =
                                   let uu____23819 =
                                     let uu____23830 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23845 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23830,
                                       uu____23845)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23819
                                    in
                                 let uu____23860 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23818,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23860)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23811
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23863 =
            let uu____23876 =
              let uu____23877 = FStar_Syntax_Subst.compress k  in
              uu____23877.FStar_Syntax_Syntax.n  in
            match uu____23876 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23922 -> (tps, k)  in
          (match uu____23863 with
           | (formals,res) ->
               let uu____23945 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23945 with
                | (formals1,res1) ->
                    let uu____23956 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23956 with
                     | (vars,guards,env',binder_decls,uu____23981) ->
                         let uu____23994 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____23994 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____24013 =
                                  let uu____24020 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____24020)  in
                                FStar_SMTEncoding_Util.mkApp uu____24013  in
                              let uu____24029 =
                                let tname_decl =
                                  let uu____24039 =
                                    let uu____24040 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____24072  ->
                                              match uu____24072 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____24085 = varops.next_id ()  in
                                    (tname, uu____24040,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____24085, false)
                                     in
                                  constructor_or_logic_type_decl uu____24039
                                   in
                                let uu____24094 =
                                  match vars with
                                  | [] ->
                                      let uu____24107 =
                                        let uu____24108 =
                                          let uu____24111 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____24111
                                           in
                                        push_free_var env1 t tname
                                          uu____24108
                                         in
                                      ([], uu____24107)
                                  | uu____24118 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____24127 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____24127
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____24141 =
                                          let uu____24148 =
                                            let uu____24149 =
                                              let uu____24164 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24164)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24149
                                             in
                                          (uu____24148,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____24141
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____24094 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____24029 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24204 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24204 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24222 =
                                               let uu____24223 =
                                                 let uu____24230 =
                                                   let uu____24231 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24231
                                                    in
                                                 (uu____24230,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24223
                                                in
                                             [uu____24222]
                                           else []  in
                                         let uu____24235 =
                                           let uu____24238 =
                                             let uu____24241 =
                                               let uu____24242 =
                                                 let uu____24249 =
                                                   let uu____24250 =
                                                     let uu____24261 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24261)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24250
                                                    in
                                                 (uu____24249,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24242
                                                in
                                             [uu____24241]  in
                                           FStar_List.append karr uu____24238
                                            in
                                         FStar_List.append decls1 uu____24235
                                      in
                                   let aux =
                                     let uu____24277 =
                                       let uu____24280 =
                                         inversion_axioms tapp vars  in
                                       let uu____24283 =
                                         let uu____24286 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24286]  in
                                       FStar_List.append uu____24280
                                         uu____24283
                                        in
                                     FStar_List.append kindingAx uu____24277
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24293,uu____24294,uu____24295,uu____24296,uu____24297)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24305,t,uu____24307,n_tps,uu____24309) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24317 = new_term_constant_and_tok_from_lid env d  in
          (match uu____24317 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____24334 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____24334 with
                | (formals,t_res) ->
                    let uu____24369 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24369 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____24383 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____24383 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____24453 =
                                            mk_term_projector_name d x  in
                                          (uu____24453,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____24455 =
                                  let uu____24474 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24474, true)
                                   in
                                FStar_All.pipe_right uu____24455
                                  FStar_SMTEncoding_Term.constructor_to_decl
                                 in
                              let app = mk_Apply ddtok_tm vars  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars
                                 in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars)
                                 in
                              let uu____24513 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____24513 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24525::uu____24526 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort)
                                            in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff
                                            in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff]  in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)]
                                            in
                                         let uu____24571 =
                                           let uu____24582 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24582)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24571
                                     | uu____24607 -> tok_typing  in
                                   let uu____24616 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____24616 with
                                    | (vars',guards',env'',decls_formals,uu____24641)
                                        ->
                                        let uu____24654 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars'
                                             in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1)
                                             in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1
                                           in
                                        (match uu____24654 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24685 ->
                                                   let uu____24692 =
                                                     let uu____24693 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24693
                                                      in
                                                   [uu____24692]
                                                in
                                             let encode_elim uu____24703 =
                                               let uu____24704 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____24704 with
                                               | (head1,args) ->
                                                   let uu____24747 =
                                                     let uu____24748 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24748.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24747 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24758;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24759;_},uu____24760)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____24766 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____24766
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____24809
                                                                    ->
                                                                    let uu____24810
                                                                    =
                                                                    let uu____24815
                                                                    =
                                                                    let uu____24816
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24816
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVaribleInductiveTypeParameter,
                                                                    uu____24815)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24810
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24832
                                                                    =
                                                                    let uu____24833
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24833
                                                                     in
                                                                    if
                                                                    uu____24832
                                                                    then
                                                                    let uu____24846
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24846]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____24848
                                                               =
                                                               let uu____24861
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24911
                                                                     ->
                                                                    fun
                                                                    uu____24912
                                                                     ->
                                                                    match 
                                                                    (uu____24911,
                                                                    uu____24912)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25007
                                                                    =
                                                                    let uu____25014
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25014
                                                                     in
                                                                    (match uu____25007
                                                                    with
                                                                    | 
                                                                    (uu____25027,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25035
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25035
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25037
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25037
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 uu____24861
                                                                in
                                                             (match uu____24848
                                                              with
                                                              | (uu____25052,arg_vars,elim_eqns_or_guards,uu____25055)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____25085
                                                                    =
                                                                    let uu____25092
                                                                    =
                                                                    let uu____25093
                                                                    =
                                                                    let uu____25104
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25115
                                                                    =
                                                                    let uu____25116
                                                                    =
                                                                    let uu____25121
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25121)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25116
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25104,
                                                                    uu____25115)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25093
                                                                     in
                                                                    (uu____25092,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25085
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25144
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25144,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25146
                                                                    =
                                                                    let uu____25153
                                                                    =
                                                                    let uu____25154
                                                                    =
                                                                    let uu____25165
                                                                    =
                                                                    let uu____25170
                                                                    =
                                                                    let uu____25173
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25173]
                                                                     in
                                                                    [uu____25170]
                                                                     in
                                                                    let uu____25178
                                                                    =
                                                                    let uu____25179
                                                                    =
                                                                    let uu____25184
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25185
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25184,
                                                                    uu____25185)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25179
                                                                     in
                                                                    (uu____25165,
                                                                    [x],
                                                                    uu____25178)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25154
                                                                     in
                                                                    let uu____25204
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25153,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25204)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25146
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25211
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____25239
                                                                    =
                                                                    let uu____25240
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25240
                                                                    dapp1  in
                                                                    [uu____25239])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25211
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25247
                                                                    =
                                                                    let uu____25254
                                                                    =
                                                                    let uu____25255
                                                                    =
                                                                    let uu____25266
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25277
                                                                    =
                                                                    let uu____25278
                                                                    =
                                                                    let uu____25283
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25283)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25278
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25266,
                                                                    uu____25277)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25255
                                                                     in
                                                                    (uu____25254,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25247)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____25304 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____25304
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               orig_arg arg
                                                               xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____25347
                                                                    ->
                                                                    let uu____25348
                                                                    =
                                                                    let uu____25353
                                                                    =
                                                                    let uu____25354
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25354
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVaribleInductiveTypeParameter,
                                                                    uu____25353)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25348
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25370
                                                                    =
                                                                    let uu____25371
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25371
                                                                     in
                                                                    if
                                                                    uu____25370
                                                                    then
                                                                    let uu____25384
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25384]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____25386
                                                               =
                                                               let uu____25399
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25449
                                                                     ->
                                                                    fun
                                                                    uu____25450
                                                                     ->
                                                                    match 
                                                                    (uu____25449,
                                                                    uu____25450)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25545
                                                                    =
                                                                    let uu____25552
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25552
                                                                     in
                                                                    (match uu____25545
                                                                    with
                                                                    | 
                                                                    (uu____25565,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25573
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25573
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25575
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25575
                                                                    ::
                                                                    eqns_or_guards)
                                                                     in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int "0"))
                                                                 uu____25399
                                                                in
                                                             (match uu____25386
                                                              with
                                                              | (uu____25590,arg_vars,elim_eqns_or_guards,uu____25593)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars
                                                                     in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1)
                                                                     in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars  in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1)
                                                                     in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty
                                                                     in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1
                                                                     in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____25623
                                                                    =
                                                                    let uu____25630
                                                                    =
                                                                    let uu____25631
                                                                    =
                                                                    let uu____25642
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25653
                                                                    =
                                                                    let uu____25654
                                                                    =
                                                                    let uu____25659
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25659)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25654
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25642,
                                                                    uu____25653)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25631
                                                                     in
                                                                    (uu____25630,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25623
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25682
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25682,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25684
                                                                    =
                                                                    let uu____25691
                                                                    =
                                                                    let uu____25692
                                                                    =
                                                                    let uu____25703
                                                                    =
                                                                    let uu____25708
                                                                    =
                                                                    let uu____25711
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25711]
                                                                     in
                                                                    [uu____25708]
                                                                     in
                                                                    let uu____25716
                                                                    =
                                                                    let uu____25717
                                                                    =
                                                                    let uu____25722
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25723
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25722,
                                                                    uu____25723)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25717
                                                                     in
                                                                    (uu____25703,
                                                                    [x],
                                                                    uu____25716)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25692
                                                                     in
                                                                    let uu____25742
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25691,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25742)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25684
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25749
                                                                    =
                                                                    FStar_All.pipe_right
                                                                    vars
                                                                    (FStar_List.mapi
                                                                    (fun i 
                                                                    ->
                                                                    fun v1 
                                                                    ->
                                                                    if
                                                                    i < n_tps
                                                                    then []
                                                                    else
                                                                    (let uu____25777
                                                                    =
                                                                    let uu____25778
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25778
                                                                    dapp1  in
                                                                    [uu____25777])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25749
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25785
                                                                    =
                                                                    let uu____25792
                                                                    =
                                                                    let uu____25793
                                                                    =
                                                                    let uu____25804
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25815
                                                                    =
                                                                    let uu____25816
                                                                    =
                                                                    let uu____25821
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25821)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25816
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25804,
                                                                    uu____25815)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25793
                                                                     in
                                                                    (uu____25792,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25785)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25840 ->
                                                        ((let uu____25842 =
                                                            let uu____25847 =
                                                              let uu____25848
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25849
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25848
                                                                uu____25849
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25847)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25842);
                                                         ([], [])))
                                                in
                                             let uu____25854 = encode_elim ()
                                                in
                                             (match uu____25854 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25874 =
                                                      let uu____25877 =
                                                        let uu____25880 =
                                                          let uu____25883 =
                                                            let uu____25886 =
                                                              let uu____25887
                                                                =
                                                                let uu____25898
                                                                  =
                                                                  let uu____25901
                                                                    =
                                                                    let uu____25902
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25902
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25901
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25898)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25887
                                                               in
                                                            [uu____25886]  in
                                                          let uu____25907 =
                                                            let uu____25910 =
                                                              let uu____25913
                                                                =
                                                                let uu____25916
                                                                  =
                                                                  let uu____25919
                                                                    =
                                                                    let uu____25922
                                                                    =
                                                                    let uu____25925
                                                                    =
                                                                    let uu____25926
                                                                    =
                                                                    let uu____25933
                                                                    =
                                                                    let uu____25934
                                                                    =
                                                                    let uu____25945
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25945)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25934
                                                                     in
                                                                    (uu____25933,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25926
                                                                     in
                                                                    let uu____25958
                                                                    =
                                                                    let uu____25961
                                                                    =
                                                                    let uu____25962
                                                                    =
                                                                    let uu____25969
                                                                    =
                                                                    let uu____25970
                                                                    =
                                                                    let uu____25981
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25992
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25981,
                                                                    uu____25992)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25970
                                                                     in
                                                                    (uu____25969,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25962
                                                                     in
                                                                    [uu____25961]
                                                                     in
                                                                    uu____25925
                                                                    ::
                                                                    uu____25958
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25922
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25919
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25916
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25913
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25910
                                                             in
                                                          FStar_List.append
                                                            uu____25883
                                                            uu____25907
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25880
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25877
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25874
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____26038  ->
              fun se  ->
                match uu____26038 with
                | (g,env1) ->
                    let uu____26058 = encode_sigelt env1 se  in
                    (match uu____26058 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____26115 =
        match uu____26115 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26147 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.Primops;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort
                    in
                 ((let uu____26153 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26153
                   then
                     let uu____26154 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26155 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26156 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26154 uu____26155 uu____26156
                   else ());
                  (let uu____26158 = encode_term t1 env1  in
                   match uu____26158 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____26174 =
                         let uu____26181 =
                           let uu____26182 =
                             let uu____26183 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____26183
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____26182  in
                         new_term_constant_from_string env1 x uu____26181  in
                       (match uu____26174 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____26199 = FStar_Options.log_queries ()
                                 in
                              if uu____26199
                              then
                                let uu____26202 =
                                  let uu____26203 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____26204 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____26205 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26203 uu____26204 uu____26205
                                   in
                                FStar_Pervasives_Native.Some uu____26202
                              else FStar_Pervasives_Native.None  in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym  in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name)
                               in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax])
                               in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26221,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26235 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26235 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26258,se,uu____26260) ->
                 let uu____26265 = encode_sigelt env1 se  in
                 (match uu____26265 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26282,se) ->
                 let uu____26288 = encode_sigelt env1 se  in
                 (match uu____26288 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26305 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26305 with | (uu____26328,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26340 'Auu____26341 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26341,'Auu____26340)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26409  ->
              match uu____26409 with
              | (l,uu____26421,uu____26422) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26468  ->
              match uu____26468 with
              | (l,uu____26482,uu____26483) ->
                  let uu____26492 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____26493 =
                    let uu____26496 =
                      let uu____26497 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____26497  in
                    [uu____26496]  in
                  uu____26492 :: uu____26493))
       in
    (prefix1, suffix)
  
let last_env : env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref [] 
let init_env : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____26518 =
      let uu____26521 =
        let uu____26522 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____26525 =
          let uu____26526 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____26526 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26522;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26525
        }  in
      [uu____26521]  in
    FStar_ST.op_Colon_Equals last_env uu____26518
  
let get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____26585 = FStar_ST.op_Bang last_env  in
      match uu____26585 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26641 ->
          let uu___362_26644 = e  in
          let uu____26645 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___362_26644.bindings);
            depth = (uu___362_26644.depth);
            tcenv;
            warn = (uu___362_26644.warn);
            cache = (uu___362_26644.cache);
            nolabels = (uu___362_26644.nolabels);
            use_zfuel_name = (uu___362_26644.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___362_26644.encode_non_total_function_typ);
            current_module_name = uu____26645
          }
  
let set_env : env_t -> Prims.unit =
  fun env  ->
    let uu____26649 = FStar_ST.op_Bang last_env  in
    match uu____26649 with
    | [] -> failwith "Empty env stack"
    | uu____26704::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let push_env : Prims.unit -> Prims.unit =
  fun uu____26762  ->
    let uu____26763 = FStar_ST.op_Bang last_env  in
    match uu____26763 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___363_26826 = hd1  in
          {
            bindings = (uu___363_26826.bindings);
            depth = (uu___363_26826.depth);
            tcenv = (uu___363_26826.tcenv);
            warn = (uu___363_26826.warn);
            cache = refs;
            nolabels = (uu___363_26826.nolabels);
            use_zfuel_name = (uu___363_26826.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___363_26826.encode_non_total_function_typ);
            current_module_name = (uu___363_26826.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let pop_env : Prims.unit -> Prims.unit =
  fun uu____26881  ->
    let uu____26882 = FStar_ST.op_Bang last_env  in
    match uu____26882 with
    | [] -> failwith "Popping an empty stack"
    | uu____26937::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let init : FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let push : Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let pop : Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg 
let open_fact_db_tags : env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> [] 
let place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____27030::uu____27031,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___364_27039 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___364_27039.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___364_27039.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___364_27039.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____27040 -> d
  
let fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____27055 =
        let uu____27058 =
          let uu____27059 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____27059  in
        let uu____27060 = open_fact_db_tags env  in uu____27058 ::
          uu____27060
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____27055
  
let encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____27082 = encode_sigelt env se  in
      match uu____27082 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____27118 = FStar_Options.log_queries ()  in
        if uu____27118
        then
          let uu____27121 =
            let uu____27122 =
              let uu____27123 =
                let uu____27124 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____27124 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____27123  in
            FStar_SMTEncoding_Term.Caption uu____27122  in
          uu____27121 :: decls
        else decls  in
      (let uu____27135 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27135
       then
         let uu____27136 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____27136
       else ());
      (let env =
         let uu____27139 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____27139 tcenv  in
       let uu____27140 = encode_top_level_facts env se  in
       match uu____27140 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____27154 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____27154)))
  
let encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____27166 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____27166
       then
         let uu____27167 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____27167
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____27202  ->
                 fun se  ->
                   match uu____27202 with
                   | (g,env2) ->
                       let uu____27222 = encode_top_level_facts env2 se  in
                       (match uu____27222 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____27245 =
         encode_signature
           (let uu___365_27254 = env  in
            {
              bindings = (uu___365_27254.bindings);
              depth = (uu___365_27254.depth);
              tcenv = (uu___365_27254.tcenv);
              warn = false;
              cache = (uu___365_27254.cache);
              nolabels = (uu___365_27254.nolabels);
              use_zfuel_name = (uu___365_27254.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___365_27254.encode_non_total_function_typ);
              current_module_name = (uu___365_27254.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____27245 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____27271 = FStar_Options.log_queries ()  in
             if uu____27271
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___366_27279 = env1  in
               {
                 bindings = (uu___366_27279.bindings);
                 depth = (uu___366_27279.depth);
                 tcenv = (uu___366_27279.tcenv);
                 warn = true;
                 cache = (uu___366_27279.cache);
                 nolabels = (uu___366_27279.nolabels);
                 use_zfuel_name = (uu___366_27279.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___366_27279.encode_non_total_function_typ);
                 current_module_name = (uu___366_27279.current_module_name)
               });
            (let uu____27281 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____27281
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let encode_query :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____27333 =
           let uu____27334 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____27334.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____27333);
        (let env =
           let uu____27336 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____27336 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____27348 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27383 = aux rest  in
                 (match uu____27383 with
                  | (out,rest1) ->
                      let t =
                        let uu____27413 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____27413 with
                        | FStar_Pervasives_Native.Some uu____27418 ->
                            let uu____27419 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____27419
                              x.FStar_Syntax_Syntax.sort
                        | uu____27420 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____27424 =
                        let uu____27427 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___367_27430 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___367_27430.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___367_27430.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____27427 :: out  in
                      (uu____27424, rest1))
             | uu____27435 -> ([], bindings1)  in
           let uu____27442 = aux bindings  in
           match uu____27442 with
           | (closing,bindings1) ->
               let uu____27467 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____27467, bindings1)
            in
         match uu____27348 with
         | (q1,bindings1) ->
             let uu____27490 =
               let uu____27495 =
                 FStar_List.filter
                   (fun uu___332_27500  ->
                      match uu___332_27500 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27501 ->
                          false
                      | uu____27508 -> true) bindings1
                  in
               encode_env_bindings env uu____27495  in
             (match uu____27490 with
              | (env_decls,env1) ->
                  ((let uu____27526 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery"))
                       in
                    if uu____27526
                    then
                      let uu____27527 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27527
                    else ());
                   (let uu____27529 = encode_formula q1 env1  in
                    match uu____27529 with
                    | (phi,qdecls) ->
                        let uu____27550 =
                          let uu____27555 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27555 phi
                           in
                        (match uu____27550 with
                         | (labels,phi1) ->
                             let uu____27572 = encode_labels labels  in
                             (match uu____27572 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____27609 =
                                      let uu____27616 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____27617 =
                                        varops.mk_unique "@query"  in
                                      (uu____27616,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27617)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27609
                                     in
                                  let suffix =
                                    FStar_List.append
                                      [FStar_SMTEncoding_Term.Echo "<labels>"]
                                      (FStar_List.append label_suffix
                                         [FStar_SMTEncoding_Term.Echo
                                            "</labels>";
                                         FStar_SMTEncoding_Term.Echo "Done!"])
                                     in
                                  (query_prelude, labels, qry, suffix)))))))
  