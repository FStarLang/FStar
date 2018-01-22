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
      (fun uu___77_107  ->
         match uu___77_107 with
         | (FStar_Util.Inl uu____116,uu____117) -> false
         | uu____122 -> true) args
  
let (escape : Prims.string -> Prims.string) =
  fun s  -> FStar_Util.replace_char s 39 95 
let (mk_term_projector_name :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string) =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___100_143 = a  in
        let uu____144 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname
           in
        {
          FStar_Syntax_Syntax.ppname = uu____144;
          FStar_Syntax_Syntax.index =
            (uu___100_143.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___100_143.FStar_Syntax_Syntax.sort)
        }  in
      let uu____145 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText
         in
      FStar_All.pipe_left escape uu____145
  
let (primitive_projector_by_pos :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string)
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____158 =
          let uu____159 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str
             in
          failwith uu____159  in
        let uu____160 = FStar_TypeChecker_Env.lookup_datacon env lid  in
        match uu____160 with
        | (uu____165,t) ->
            let uu____167 =
              let uu____168 = FStar_Syntax_Subst.compress t  in
              uu____168.FStar_Syntax_Syntax.n  in
            (match uu____167 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____189 = FStar_Syntax_Subst.open_comp bs c  in
                 (match uu____189 with
                  | (binders,uu____195) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i  in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____210 -> fail ())
  
let (mk_term_projector_name_by_pos :
  FStar_Ident.lident -> Prims.int -> Prims.string) =
  fun lid  ->
    fun i  ->
      let uu____217 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i)
         in
      FStar_All.pipe_left escape uu____217
  
let (mk_term_projector :
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term)
  =
  fun lid  ->
    fun a  ->
      let uu____224 =
        let uu____229 = mk_term_projector_name lid a  in
        (uu____229,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____224
  
let (mk_term_projector_by_pos :
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term) =
  fun lid  ->
    fun i  ->
      let uu____236 =
        let uu____241 = mk_term_projector_name_by_pos lid i  in
        (uu____241,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort)))
         in
      FStar_SMTEncoding_Util.mkFreeV uu____236
  
let mk_data_tester :
  'Auu____246 .
    'Auu____246 ->
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
let (__proj__Mkvarops_t__item__push : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__push
  
let (__proj__Mkvarops_t__item__pop : varops_t -> Prims.unit -> Prims.unit) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__pop
  
let (__proj__Mkvarops_t__item__new_var :
  varops_t -> FStar_Ident.ident -> Prims.int -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_var
  
let (__proj__Mkvarops_t__item__new_fvar :
  varops_t -> FStar_Ident.lident -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__new_fvar
  
let (__proj__Mkvarops_t__item__fresh :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__fresh
  
let (__proj__Mkvarops_t__item__string_const :
  varops_t -> Prims.string -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__string_const
  
let (__proj__Mkvarops_t__item__next_id : varops_t -> Prims.unit -> Prims.int)
  =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__next_id
  
let (__proj__Mkvarops_t__item__mk_unique :
  varops_t -> Prims.string -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { push = __fname__push; pop = __fname__pop; new_var = __fname__new_var;
        new_fvar = __fname__new_fvar; fresh = __fname__fresh;
        string_const = __fname__string_const; next_id = __fname__next_id;
        mk_unique = __fname__mk_unique;_} -> __fname__mk_unique
  
let (varops : varops_t) =
  let initial_ctr = (Prims.parse_int "100")  in
  let ctr = FStar_Util.mk_ref initial_ctr  in
  let new_scope uu____610 =
    let uu____611 = FStar_Util.smap_create (Prims.parse_int "100")  in
    let uu____614 = FStar_Util.smap_create (Prims.parse_int "100")  in
    (uu____611, uu____614)  in
  let scopes =
    let uu____634 = let uu____645 = new_scope ()  in [uu____645]  in
    FStar_Util.mk_ref uu____634  in
  let mk_unique y =
    let y1 = escape y  in
    let y2 =
      let uu____686 =
        let uu____689 = FStar_ST.op_Bang scopes  in
        FStar_Util.find_map uu____689
          (fun uu____772  ->
             match uu____772 with
             | (names1,uu____784) -> FStar_Util.smap_try_find names1 y1)
         in
      match uu____686 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____793 ->
          (FStar_Util.incr ctr;
           (let uu____828 =
              let uu____829 =
                let uu____830 = FStar_ST.op_Bang ctr  in
                Prims.string_of_int uu____830  in
              Prims.strcat "__" uu____829  in
            Prims.strcat y1 uu____828))
       in
    let top_scope =
      let uu____875 =
        let uu____884 = FStar_ST.op_Bang scopes  in FStar_List.hd uu____884
         in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____875  in
    FStar_Util.smap_add top_scope y2 true; y2  in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn)))
     in
  let new_fvar lid = mk_unique lid.FStar_Ident.str  in
  let next_id1 uu____993 = FStar_Util.incr ctr; FStar_ST.op_Bang ctr  in
  let fresh1 pfx =
    let uu____1073 =
      let uu____1074 = next_id1 ()  in
      FStar_All.pipe_left Prims.string_of_int uu____1074  in
    FStar_Util.format2 "%s_%s" pfx uu____1073  in
  let string_const s =
    let uu____1079 =
      let uu____1082 = FStar_ST.op_Bang scopes  in
      FStar_Util.find_map uu____1082
        (fun uu____1165  ->
           match uu____1165 with
           | (uu____1176,strings) -> FStar_Util.smap_try_find strings s)
       in
    match uu____1079 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id1 = next_id1 ()  in
        let f =
          let uu____1189 = FStar_SMTEncoding_Util.mk_String_const id1  in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____1189  in
        let top_scope =
          let uu____1193 =
            let uu____1202 = FStar_ST.op_Bang scopes  in
            FStar_List.hd uu____1202  in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____1193  in
        (FStar_Util.smap_add top_scope s f; f)
     in
  let push1 uu____1300 =
    let uu____1301 =
      let uu____1312 = new_scope ()  in
      let uu____1321 = FStar_ST.op_Bang scopes  in uu____1312 :: uu____1321
       in
    FStar_ST.op_Colon_Equals scopes uu____1301  in
  let pop1 uu____1465 =
    let uu____1466 =
      let uu____1477 = FStar_ST.op_Bang scopes  in FStar_List.tl uu____1477
       in
    FStar_ST.op_Colon_Equals scopes uu____1466  in
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
let (unmangle : FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv) =
  fun x  ->
    let uu___101_1621 = x  in
    let uu____1622 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname  in
    {
      FStar_Syntax_Syntax.ppname = uu____1622;
      FStar_Syntax_Syntax.index = (uu___101_1621.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___101_1621.FStar_Syntax_Syntax.sort)
    }
  
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2 
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4 [@@deriving show]
let (uu___is_Binding_var : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____1655 -> false
  
let (__proj__Binding_var__item___0 :
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2)
  = fun projectee  -> match projectee with | Binding_var _0 -> _0 
let (uu___is_Binding_fvar : binding -> Prims.bool) =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____1691 -> false
  
let (__proj__Binding_fvar__item___0 :
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0 
let binder_of_eithervar :
  'Auu____1738 'Auu____1739 .
    'Auu____1739 ->
      ('Auu____1739,'Auu____1738 FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple2
  = fun v1  -> (v1, FStar_Pervasives_Native.None) 
type cache_entry =
  {
  cache_symbol_name: Prims.string ;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list ;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list ;
  cache_symbol_assumption_names: Prims.string Prims.list }[@@deriving show]
let (__proj__Mkcache_entry__item__cache_symbol_name :
  cache_entry -> Prims.string) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_name
  
let (__proj__Mkcache_entry__item__cache_symbol_arg_sorts :
  cache_entry -> FStar_SMTEncoding_Term.sort Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_arg_sorts
  
let (__proj__Mkcache_entry__item__cache_symbol_decls :
  cache_entry -> FStar_SMTEncoding_Term.decl Prims.list) =
  fun projectee  ->
    match projectee with
    | { cache_symbol_name = __fname__cache_symbol_name;
        cache_symbol_arg_sorts = __fname__cache_symbol_arg_sorts;
        cache_symbol_decls = __fname__cache_symbol_decls;
        cache_symbol_assumption_names =
          __fname__cache_symbol_assumption_names;_}
        -> __fname__cache_symbol_decls
  
let (__proj__Mkcache_entry__item__cache_symbol_assumption_names :
  cache_entry -> Prims.string Prims.list) =
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
let (__proj__Mkenv_t__item__bindings : env_t -> binding Prims.list) =
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
  
let (__proj__Mkenv_t__item__depth : env_t -> Prims.int) =
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
  
let (__proj__Mkenv_t__item__tcenv : env_t -> FStar_TypeChecker_Env.env) =
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
  
let (__proj__Mkenv_t__item__warn : env_t -> Prims.bool) =
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
  
let (__proj__Mkenv_t__item__cache : env_t -> cache_entry FStar_Util.smap) =
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
  
let (__proj__Mkenv_t__item__nolabels : env_t -> Prims.bool) =
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
  
let (__proj__Mkenv_t__item__use_zfuel_name : env_t -> Prims.bool) =
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
  
let (__proj__Mkenv_t__item__encode_non_total_function_typ :
  env_t -> Prims.bool) =
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
  
let (__proj__Mkenv_t__item__current_module_name : env_t -> Prims.string) =
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
  'Auu____2035 .
    'Auu____2035 ->
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
                 (fun uu___78_2069  ->
                    match uu___78_2069 with
                    | FStar_SMTEncoding_Term.Assume a ->
                        [a.FStar_SMTEncoding_Term.assumption_name]
                    | uu____2073 -> []))
             in
          {
            cache_symbol_name = tsym;
            cache_symbol_arg_sorts = cvar_sorts;
            cache_symbol_decls = t_decls;
            cache_symbol_assumption_names = names1
          }
  
let (use_cache_entry : cache_entry -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
  
let (print_env : env_t -> Prims.string) =
  fun e  ->
    let uu____2082 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___79_2092  ->
              match uu___79_2092 with
              | Binding_var (x,uu____2094) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____2096,uu____2097,uu____2098) ->
                  FStar_Syntax_Print.lid_to_string l))
       in
    FStar_All.pipe_right uu____2082 (FStar_String.concat ", ")
  
let lookup_binding :
  'Auu____2112 .
    env_t ->
      (binding -> 'Auu____2112 FStar_Pervasives_Native.option) ->
        'Auu____2112 FStar_Pervasives_Native.option
  = fun env  -> fun f  -> FStar_Util.find_map env.bindings f 
let (caption_t :
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun t  ->
      let uu____2140 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
      if uu____2140
      then
        let uu____2143 = FStar_Syntax_Print.term_to_string t  in
        FStar_Pervasives_Native.Some uu____2143
      else FStar_Pervasives_Native.None
  
let (fresh_fvar :
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x  in
      let uu____2156 = FStar_SMTEncoding_Util.mkFreeV (xsym, s)  in
      (xsym, uu____2156)
  
let (gen_term_var :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth)  in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort)
         in
      (ysym, y,
        (let uu___102_2172 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___102_2172.tcenv);
           warn = (uu___102_2172.warn);
           cache = (uu___102_2172.cache);
           nolabels = (uu___102_2172.nolabels);
           use_zfuel_name = (uu___102_2172.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___102_2172.encode_non_total_function_typ);
           current_module_name = (uu___102_2172.current_module_name)
         }))
  
let (new_term_constant :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index
         in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
      (ysym, y,
        (let uu___103_2190 = env  in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___103_2190.depth);
           tcenv = (uu___103_2190.tcenv);
           warn = (uu___103_2190.warn);
           cache = (uu___103_2190.cache);
           nolabels = (uu___103_2190.nolabels);
           use_zfuel_name = (uu___103_2190.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___103_2190.encode_non_total_function_typ);
           current_module_name = (uu___103_2190.current_module_name)
         }))
  
let (new_term_constant_from_string :
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str  in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, [])  in
        (ysym, y,
          (let uu___104_2211 = env  in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___104_2211.depth);
             tcenv = (uu___104_2211.tcenv);
             warn = (uu___104_2211.warn);
             cache = (uu___104_2211.cache);
             nolabels = (uu___104_2211.nolabels);
             use_zfuel_name = (uu___104_2211.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___104_2211.encode_non_total_function_typ);
             current_module_name = (uu___104_2211.current_module_name)
           }))
  
let (push_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t) =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___105_2221 = env  in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___105_2221.depth);
          tcenv = (uu___105_2221.tcenv);
          warn = (uu___105_2221.warn);
          cache = (uu___105_2221.cache);
          nolabels = (uu___105_2221.nolabels);
          use_zfuel_name = (uu___105_2221.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___105_2221.encode_non_total_function_typ);
          current_module_name = (uu___105_2221.current_module_name)
        }
  
let (lookup_term_var :
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term) =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___80_2245  ->
             match uu___80_2245 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____2258 -> FStar_Pervasives_Native.None)
         in
      let uu____2263 = aux a  in
      match uu____2263 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a  in
          let uu____2275 = aux a2  in
          (match uu____2275 with
           | FStar_Pervasives_Native.None  ->
               let uu____2286 =
                 let uu____2287 = FStar_Syntax_Print.bv_to_string a2  in
                 let uu____2288 = print_env env  in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____2287 uu____2288
                  in
               failwith uu____2286
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
  
let (new_term_constant_and_tok_from_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x  in
      let ftok = Prims.strcat fname "@tok"  in
      let uu____2315 =
        let uu___106_2316 = env  in
        let uu____2317 =
          let uu____2320 =
            let uu____2321 =
              let uu____2334 =
                let uu____2337 = FStar_SMTEncoding_Util.mkApp (ftok, [])  in
                FStar_All.pipe_left
                  (fun _0_40  -> FStar_Pervasives_Native.Some _0_40)
                  uu____2337
                 in
              (x, fname, uu____2334, FStar_Pervasives_Native.None)  in
            Binding_fvar uu____2321  in
          uu____2320 :: (env.bindings)  in
        {
          bindings = uu____2317;
          depth = (uu___106_2316.depth);
          tcenv = (uu___106_2316.tcenv);
          warn = (uu___106_2316.warn);
          cache = (uu___106_2316.cache);
          nolabels = (uu___106_2316.nolabels);
          use_zfuel_name = (uu___106_2316.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___106_2316.encode_non_total_function_typ);
          current_module_name = (uu___106_2316.current_module_name)
        }  in
      (fname, ftok, uu____2315)
  
let (try_lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3 FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___81_2379  ->
           match uu___81_2379 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____2418 -> FStar_Pervasives_Native.None)
  
let (contains_name : env_t -> Prims.string -> Prims.bool) =
  fun env  ->
    fun s  ->
      let uu____2435 =
        lookup_binding env
          (fun uu___82_2443  ->
             match uu___82_2443 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____2458 -> FStar_Pervasives_Native.None)
         in
      FStar_All.pipe_right uu____2435 FStar_Option.isSome
  
let (lookup_lid :
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun a  ->
      let uu____2477 = try_lookup_lid env a  in
      match uu____2477 with
      | FStar_Pervasives_Native.None  ->
          let uu____2510 =
            let uu____2511 = FStar_Syntax_Print.lid_to_string a  in
            FStar_Util.format1 "Name not found: %s" uu____2511  in
          failwith uu____2510
      | FStar_Pervasives_Native.Some s -> s
  
let (push_free_var :
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t)
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___107_2559 = env  in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___107_2559.depth);
            tcenv = (uu___107_2559.tcenv);
            warn = (uu___107_2559.warn);
            cache = (uu___107_2559.cache);
            nolabels = (uu___107_2559.nolabels);
            use_zfuel_name = (uu___107_2559.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___107_2559.encode_non_total_function_typ);
            current_module_name = (uu___107_2559.current_module_name)
          }
  
let (push_zfuel_name : env_t -> FStar_Ident.lident -> Prims.string -> env_t)
  =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____2573 = lookup_lid env x  in
        match uu____2573 with
        | (t1,t2,uu____2586) ->
            let t3 =
              let uu____2596 =
                let uu____2603 =
                  let uu____2606 = FStar_SMTEncoding_Util.mkApp ("ZFuel", [])
                     in
                  [uu____2606]  in
                (f, uu____2603)  in
              FStar_SMTEncoding_Util.mkApp uu____2596  in
            let uu___108_2611 = env  in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___108_2611.depth);
              tcenv = (uu___108_2611.tcenv);
              warn = (uu___108_2611.warn);
              cache = (uu___108_2611.cache);
              nolabels = (uu___108_2611.nolabels);
              use_zfuel_name = (uu___108_2611.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___108_2611.encode_non_total_function_typ);
              current_module_name = (uu___108_2611.current_module_name)
            }
  
let (try_lookup_free_var :
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun l  ->
      let uu____2624 = try_lookup_lid env l  in
      match uu____2624 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____2673 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____2681,fuel::[]) ->
                         let uu____2685 =
                           let uu____2686 =
                             let uu____2687 =
                               FStar_SMTEncoding_Term.fv_of_term fuel  in
                             FStar_All.pipe_right uu____2687
                               FStar_Pervasives_Native.fst
                              in
                           FStar_Util.starts_with uu____2686 "fuel"  in
                         if uu____2685
                         then
                           let uu____2690 =
                             let uu____2691 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort)
                                in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____2691
                               fuel
                              in
                           FStar_All.pipe_left
                             (fun _0_41  ->
                                FStar_Pervasives_Native.Some _0_41)
                             uu____2690
                         else FStar_Pervasives_Native.Some t
                     | uu____2695 -> FStar_Pervasives_Native.Some t)
                | uu____2696 -> FStar_Pervasives_Native.None))
  
let (lookup_free_var :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      FStar_SMTEncoding_Term.term)
  =
  fun env  ->
    fun a  ->
      let uu____2709 = try_lookup_free_var env a.FStar_Syntax_Syntax.v  in
      match uu____2709 with
      | FStar_Pervasives_Native.Some t -> t
      | FStar_Pervasives_Native.None  ->
          let uu____2713 =
            let uu____2714 =
              FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v  in
            FStar_Util.format1 "Name not found: %s" uu____2714  in
          failwith uu____2713
  
let (lookup_free_var_name :
  env_t -> FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t -> Prims.string)
  =
  fun env  ->
    fun a  ->
      let uu____2725 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____2725 with | (x,uu____2737,uu____2738) -> x
  
let (lookup_free_var_sym :
  env_t ->
    FStar_Ident.lident FStar_Syntax_Syntax.withinfo_t ->
      (FStar_SMTEncoding_Term.op,FStar_SMTEncoding_Term.term Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun a  ->
      let uu____2763 = lookup_lid env a.FStar_Syntax_Syntax.v  in
      match uu____2763 with
      | (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some
               {
                 FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App
                   (g,zf);
                 FStar_SMTEncoding_Term.freevars = uu____2799;
                 FStar_SMTEncoding_Term.rng = uu____2800;_}
               when env.use_zfuel_name -> (g, zf)
           | uu____2815 ->
               (match sym with
                | FStar_Pervasives_Native.None  ->
                    ((FStar_SMTEncoding_Term.Var name), [])
                | FStar_Pervasives_Native.Some sym1 ->
                    (match sym1.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                     | uu____2839 -> ((FStar_SMTEncoding_Term.Var name), []))))
  
let (tok_of_name :
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___83_2855  ->
           match uu___83_2855 with
           | Binding_fvar (uu____2858,nm',tok,uu____2861) when nm = nm' ->
               tok
           | uu____2870 -> FStar_Pervasives_Native.None)
  
let mkForall_fuel' :
  'Auu____2874 .
    'Auu____2874 ->
      (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
        FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
        FStar_SMTEncoding_Term.term
  =
  fun n1  ->
    fun uu____2892  ->
      match uu____2892 with
      | (pats,vars,body) ->
          let fallback uu____2917 =
            FStar_SMTEncoding_Util.mkForall (pats, vars, body)  in
          let uu____2922 = FStar_Options.unthrottle_inductives ()  in
          if uu____2922
          then fallback ()
          else
            (let uu____2924 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
                in
             match uu____2924 with
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
                           | uu____2955 -> p))
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
                             let uu____2976 = add_fuel1 guards  in
                             FStar_SMTEncoding_Util.mk_and_l uu____2976
                         | uu____2979 ->
                             let uu____2980 = add_fuel1 [guard]  in
                             FStar_All.pipe_right uu____2980 FStar_List.hd
                          in
                       FStar_SMTEncoding_Util.mkImp (guard1, body')
                   | uu____2985 -> body  in
                 let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars
                    in
                 FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
  
let (mkForall_fuel :
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term)
  = mkForall_fuel' (Prims.parse_int "1") 
let (head_normal : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t  in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____3026 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____3039 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____3046 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____3047 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____3064 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____3081 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3083 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3083 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.pos = uu____3101;
             FStar_Syntax_Syntax.vars = uu____3102;_},uu____3103)
          ->
          let uu____3124 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3124 FStar_Option.isNone
      | uu____3141 -> false
  
let (head_redex : env_t -> FStar_Syntax_Syntax.term -> Prims.bool) =
  fun env  ->
    fun t  ->
      let uu____3148 =
        let uu____3149 = FStar_Syntax_Util.un_uinst t  in
        uu____3149.FStar_Syntax_Syntax.n  in
      match uu____3148 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____3152,uu____3153,FStar_Pervasives_Native.Some rc) ->
          ((FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
              FStar_Parser_Const.effect_Tot_lid)
             ||
             (FStar_Ident.lid_equals rc.FStar_Syntax_Syntax.residual_effect
                FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___84_3174  ->
                  match uu___84_3174 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____3175 -> false)
               rc.FStar_Syntax_Syntax.residual_flags)
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____3177 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          FStar_All.pipe_right uu____3177 FStar_Option.isSome
      | uu____3194 -> false
  
let (whnf : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      let uu____3201 = head_normal env t  in
      if uu____3201
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
  
let (norm : env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
  
let (trivial_post : FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term) =
  fun t  ->
    let uu____3212 =
      let uu____3213 = FStar_Syntax_Syntax.null_binder t  in [uu____3213]  in
    let uu____3214 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None
       in
    FStar_Syntax_Util.abs uu____3212 uu____3214 FStar_Pervasives_Native.None
  
let (mk_Apply :
  FStar_SMTEncoding_Term.term ->
    (Prims.string,FStar_SMTEncoding_Term.sort) FStar_Pervasives_Native.tuple2
      Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match FStar_Pervasives_Native.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____3252 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____3252
                | s ->
                    let uu____3257 = FStar_SMTEncoding_Util.mkFreeV var  in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____3257) e)
  
let (mk_Apply_args :
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term)
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
  
let (is_app : FStar_SMTEncoding_Term.op -> Prims.bool) =
  fun uu___85_3272  ->
    match uu___85_3272 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____3273 -> false
  
let (is_an_eta_expansion :
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
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
                       FStar_SMTEncoding_Term.freevars = uu____3309;
                       FStar_SMTEncoding_Term.rng = uu____3310;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____3333) ->
              let uu____3342 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____3353 -> false) args (FStar_List.rev xs))
                 in
              if uu____3342
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____3357,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t  in
              let uu____3361 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____3365 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars
                           in
                        Prims.op_Negation uu____3365))
                 in
              if uu____3361
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____3369 -> FStar_Pervasives_Native.None  in
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
let (__proj__Mkpattern__item__pat_vars :
  pattern ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_vars
  
let (__proj__Mkpattern__item__pat_term :
  pattern ->
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__pat_term
  
let (__proj__Mkpattern__item__guard :
  pattern -> FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__guard
  
let (__proj__Mkpattern__item__projections :
  pattern ->
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list)
  =
  fun projectee  ->
    match projectee with
    | { pat_vars = __fname__pat_vars; pat_term = __fname__pat_term;
        guard = __fname__guard; projections = __fname__projections;_} ->
        __fname__projections
  
exception Let_rec_unencodeable 
let (uu___is_Let_rec_unencodeable : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____3591 -> false
  
exception Inner_let_rec 
let (uu___is_Inner_let_rec : Prims.exn -> Prims.bool) =
  fun projectee  ->
    match projectee with | Inner_let_rec  -> true | uu____3595 -> false
  
let (as_function_typ :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.term)
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t  in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____3614 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____3627 ->
            let uu____3634 = FStar_Syntax_Util.unrefine t1  in
            aux true uu____3634
        | uu____3635 ->
            if norm1
            then let uu____3636 = whnf env t1  in aux false uu____3636
            else
              (let uu____3638 =
                 let uu____3639 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos  in
                 let uu____3640 = FStar_Syntax_Print.term_to_string t0  in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____3639 uu____3640
                  in
               failwith uu____3638)
         in
      aux true t0
  
let rec (curried_arrow_formals_comp :
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k  in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | FStar_Syntax_Syntax.Tm_refine (bv,uu____3672) ->
        curried_arrow_formals_comp bv.FStar_Syntax_Syntax.sort
    | uu____3677 ->
        let uu____3678 = FStar_Syntax_Syntax.mk_Total k1  in ([], uu____3678)
  
let is_arithmetic_primitive :
  'Auu____3692 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      'Auu____3692 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3712::uu____3713::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,uu____3717::[]) ->
          FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
      | uu____3720 -> false
  
let (isInteger : FStar_Syntax_Syntax.term' -> Prims.bool) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> true
    | uu____3741 -> false
  
let (getInteger : FStar_Syntax_Syntax.term' -> Prims.int) =
  fun tm  ->
    match tm with
    | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_int
        (n1,FStar_Pervasives_Native.None )) -> FStar_Util.int_of_string n1
    | uu____3756 -> failwith "Expected an Integer term"
  
let is_BitVector_primitive :
  'Auu____3760 .
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      (FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax,'Auu____3760)
        FStar_Pervasives_Native.tuple2 Prims.list -> Prims.bool
  =
  fun head1  ->
    fun args  ->
      match ((head1.FStar_Syntax_Syntax.n), args) with
      | (FStar_Syntax_Syntax.Tm_fvar
         fv,(sz_arg,uu____3799)::uu____3800::uu____3801::[]) ->
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
      | (FStar_Syntax_Syntax.Tm_fvar fv,(sz_arg,uu____3852)::uu____3853::[])
          ->
          ((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.nat_to_bv_lid)
             ||
             (FStar_Syntax_Syntax.fv_eq_lid fv
                FStar_Parser_Const.bv_to_nat_lid))
            && (isInteger sz_arg.FStar_Syntax_Syntax.n)
      | uu____3890 -> false
  
let rec (encode_const :
  FStar_Const.sconst ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun c  ->
    fun env  ->
      match c with
      | FStar_Const.Const_unit  -> (FStar_SMTEncoding_Term.mk_Term_unit, [])
      | FStar_Const.Const_bool (true ) ->
          let uu____4109 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue  in
          (uu____4109, [])
      | FStar_Const.Const_bool (false ) ->
          let uu____4112 =
            FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse  in
          (uu____4112, [])
      | FStar_Const.Const_char c1 ->
          let uu____4116 =
            let uu____4117 =
              let uu____4124 =
                let uu____4127 =
                  let uu____4128 =
                    FStar_SMTEncoding_Util.mkInteger'
                      (FStar_Util.int_of_char c1)
                     in
                  FStar_SMTEncoding_Term.boxInt uu____4128  in
                [uu____4127]  in
              ("FStar.Char.__char_of_int", uu____4124)  in
            FStar_SMTEncoding_Util.mkApp uu____4117  in
          (uu____4116, [])
      | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
          let uu____4144 =
            let uu____4145 = FStar_SMTEncoding_Util.mkInteger i  in
            FStar_SMTEncoding_Term.boxInt uu____4145  in
          (uu____4144, [])
      | FStar_Const.Const_int (repr,FStar_Pervasives_Native.Some sw) ->
          let syntax_term =
            FStar_ToSyntax_ToSyntax.desugar_machine_integer
              (env.tcenv).FStar_TypeChecker_Env.dsenv repr sw
              FStar_Range.dummyRange
             in
          encode_term syntax_term env
      | FStar_Const.Const_string (s,uu____4166) ->
          let uu____4167 = varops.string_const s  in (uu____4167, [])
      | FStar_Const.Const_range uu____4170 ->
          let uu____4171 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          (uu____4171, [])
      | FStar_Const.Const_effect  ->
          (FStar_SMTEncoding_Term.mk_Term_type, [])
      | c1 ->
          let uu____4177 =
            let uu____4178 = FStar_Syntax_Print.const_to_string c1  in
            FStar_Util.format1 "Unhandled constant: %s" uu____4178  in
          failwith uu____4177

and (encode_binders :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list,FStar_SMTEncoding_Term.term
                                                Prims.list,env_t,FStar_SMTEncoding_Term.decls_t,
          FStar_Syntax_Syntax.bv Prims.list) FStar_Pervasives_Native.tuple5)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____4207 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
         if uu____4207
         then
           let uu____4208 = FStar_Syntax_Print.binders_to_string ", " bs  in
           FStar_Util.print1 "Encoding binders %s\n" uu____4208
         else ());
        (let uu____4210 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____4294  ->
                   fun b  ->
                     match uu____4294 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____4373 =
                           let x = unmangle (FStar_Pervasives_Native.fst b)
                              in
                           let uu____4389 = gen_term_var env1 x  in
                           match uu____4389 with
                           | (xxsym,xx,env') ->
                               let uu____4413 =
                                 let uu____4418 =
                                   norm env1 x.FStar_Syntax_Syntax.sort  in
                                 encode_term_pred fuel_opt uu____4418 env1 xx
                                  in
                               (match uu____4413 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x))
                            in
                         (match uu____4373 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], []))
            in
         match uu____4210 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))

and (encode_term_pred :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4577 = encode_term t env  in
          match uu____4577 with
          | (t1,decls) ->
              let uu____4588 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1  in
              (uu____4588, decls)

and (encode_term_pred' :
  FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
            FStar_Pervasives_Native.tuple2)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____4599 = encode_term t env  in
          match uu____4599 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____4614 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1
                      in
                   (uu____4614, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____4616 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1  in
                   (uu____4616, decls))

and (encode_arith_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4622 = encode_args args_e env  in
        match uu____4622 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____4641 -> failwith "Impossible"  in
            let unary arg_tms1 =
              let uu____4650 = FStar_List.hd arg_tms1  in
              FStar_SMTEncoding_Term.unboxInt uu____4650  in
            let binary arg_tms1 =
              let uu____4663 =
                let uu____4664 = FStar_List.hd arg_tms1  in
                FStar_SMTEncoding_Term.unboxInt uu____4664  in
              let uu____4665 =
                let uu____4666 =
                  let uu____4667 = FStar_List.tl arg_tms1  in
                  FStar_List.hd uu____4667  in
                FStar_SMTEncoding_Term.unboxInt uu____4666  in
              (uu____4663, uu____4665)  in
            let mk_default uu____4673 =
              let uu____4674 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name
                 in
              match uu____4674 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms))
               in
            let mk_l op mk_args ts =
              let uu____4725 = FStar_Options.smtencoding_l_arith_native ()
                 in
              if uu____4725
              then
                let uu____4726 =
                  let uu____4727 = mk_args ts  in op uu____4727  in
                FStar_All.pipe_right uu____4726 FStar_SMTEncoding_Term.boxInt
              else mk_default ()  in
            let mk_nl nm op ts =
              let uu____4756 = FStar_Options.smtencoding_nl_arith_wrapped ()
                 in
              if uu____4756
              then
                let uu____4757 = binary ts  in
                match uu____4757 with
                | (t1,t2) ->
                    let uu____4764 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2])  in
                    FStar_All.pipe_right uu____4764
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____4768 =
                   FStar_Options.smtencoding_nl_arith_native ()  in
                 if uu____4768
                 then
                   let uu____4769 = op (binary ts)  in
                   FStar_All.pipe_right uu____4769
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
            let uu____4900 =
              let uu____4909 =
                FStar_List.tryFind
                  (fun uu____4931  ->
                     match uu____4931 with
                     | (l,uu____4941) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops
                 in
              FStar_All.pipe_right uu____4909 FStar_Util.must  in
            (match uu____4900 with
             | (uu____4980,op) ->
                 let uu____4990 = op arg_tms  in (uu____4990, decls))

and (encode_BitVector_term :
  env_t ->
    FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.arg Prims.list ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____4998 = FStar_List.hd args_e  in
        match uu____4998 with
        | (tm_sz,uu____5006) ->
            let sz = getInteger tm_sz.FStar_Syntax_Syntax.n  in
            let sz_key =
              FStar_Util.format1 "BitVector_%s" (Prims.string_of_int sz)  in
            let sz_decls =
              let uu____5016 = FStar_Util.smap_try_find env.cache sz_key  in
              match uu____5016 with
              | FStar_Pervasives_Native.Some cache_entry -> []
              | FStar_Pervasives_Native.None  ->
                  let t_decls = FStar_SMTEncoding_Term.mkBvConstructor sz  in
                  ((let uu____5024 = mk_cache_entry env "" [] []  in
                    FStar_Util.smap_add env.cache sz_key uu____5024);
                   t_decls)
               in
            let uu____5025 =
              match ((head1.FStar_Syntax_Syntax.n), args_e) with
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5045::(sz_arg,uu____5047)::uu____5048::[]) when
                  (FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.bv_uext_lid)
                    && (isInteger sz_arg.FStar_Syntax_Syntax.n)
                  ->
                  let uu____5097 =
                    let uu____5100 = FStar_List.tail args_e  in
                    FStar_List.tail uu____5100  in
                  let uu____5103 =
                    let uu____5106 = getInteger sz_arg.FStar_Syntax_Syntax.n
                       in
                    FStar_Pervasives_Native.Some uu____5106  in
                  (uu____5097, uu____5103)
              | (FStar_Syntax_Syntax.Tm_fvar
                 fv,uu____5112::(sz_arg,uu____5114)::uu____5115::[]) when
                  FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.bv_uext_lid
                  ->
                  let uu____5164 =
                    let uu____5165 = FStar_Syntax_Print.term_to_string sz_arg
                       in
                    FStar_Util.format1
                      "Not a constant bitvector extend size: %s" uu____5165
                     in
                  failwith uu____5164
              | uu____5174 ->
                  let uu____5181 = FStar_List.tail args_e  in
                  (uu____5181, FStar_Pervasives_Native.None)
               in
            (match uu____5025 with
             | (arg_tms,ext_sz) ->
                 let uu____5204 = encode_args arg_tms env  in
                 (match uu____5204 with
                  | (arg_tms1,decls) ->
                      let head_fv =
                        match head1.FStar_Syntax_Syntax.n with
                        | FStar_Syntax_Syntax.Tm_fvar fv -> fv
                        | uu____5225 -> failwith "Impossible"  in
                      let unary arg_tms2 =
                        let uu____5234 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxBitVec sz uu____5234  in
                      let unary_arith arg_tms2 =
                        let uu____5243 = FStar_List.hd arg_tms2  in
                        FStar_SMTEncoding_Term.unboxInt uu____5243  in
                      let binary arg_tms2 =
                        let uu____5256 =
                          let uu____5257 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5257
                           in
                        let uu____5258 =
                          let uu____5259 =
                            let uu____5260 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5260  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5259
                           in
                        (uu____5256, uu____5258)  in
                      let binary_arith arg_tms2 =
                        let uu____5275 =
                          let uu____5276 = FStar_List.hd arg_tms2  in
                          FStar_SMTEncoding_Term.unboxBitVec sz uu____5276
                           in
                        let uu____5277 =
                          let uu____5278 =
                            let uu____5279 = FStar_List.tl arg_tms2  in
                            FStar_List.hd uu____5279  in
                          FStar_SMTEncoding_Term.unboxInt uu____5278  in
                        (uu____5275, uu____5277)  in
                      let mk_bv op mk_args resBox ts =
                        let uu____5328 =
                          let uu____5329 = mk_args ts  in op uu____5329  in
                        FStar_All.pipe_right uu____5328 resBox  in
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
                        let uu____5437 =
                          let uu____5440 =
                            match ext_sz with
                            | FStar_Pervasives_Native.Some x -> x
                            | FStar_Pervasives_Native.None  ->
                                failwith "impossible"
                             in
                          FStar_SMTEncoding_Util.mkBvUext uu____5440  in
                        let uu____5442 =
                          let uu____5445 =
                            let uu____5446 =
                              match ext_sz with
                              | FStar_Pervasives_Native.Some x -> x
                              | FStar_Pervasives_Native.None  ->
                                  failwith "impossible"
                               in
                            sz + uu____5446  in
                          FStar_SMTEncoding_Term.boxBitVec uu____5445  in
                        mk_bv uu____5437 unary uu____5442 arg_tms2  in
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
                      let uu____5645 =
                        let uu____5654 =
                          FStar_List.tryFind
                            (fun uu____5676  ->
                               match uu____5676 with
                               | (l,uu____5686) ->
                                   FStar_Syntax_Syntax.fv_eq_lid head_fv l)
                            ops
                           in
                        FStar_All.pipe_right uu____5654 FStar_Util.must  in
                      (match uu____5645 with
                       | (uu____5727,op) ->
                           let uu____5737 = op arg_tms1  in
                           (uu____5737, (FStar_List.append sz_decls decls)))))

and (encode_term :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t  in
      (let uu____5748 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding")
          in
       if uu____5748
       then
         let uu____5749 = FStar_Syntax_Print.tag_of_term t  in
         let uu____5750 = FStar_Syntax_Print.tag_of_term t0  in
         let uu____5751 = FStar_Syntax_Print.term_to_string t0  in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____5749 uu____5750
           uu____5751
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____5757 ->
           let uu____5782 =
             let uu____5783 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5784 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5785 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5786 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5783
               uu____5784 uu____5785 uu____5786
              in
           failwith uu____5782
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____5791 =
             let uu____5792 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos
                in
             let uu____5793 = FStar_Syntax_Print.tag_of_term t0  in
             let uu____5794 = FStar_Syntax_Print.term_to_string t0  in
             let uu____5795 = FStar_Syntax_Print.term_to_string t  in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____5792
               uu____5793 uu____5794 uu____5795
              in
           failwith uu____5791
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____5801 =
             let uu____5802 = FStar_Syntax_Print.bv_to_string x  in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____5802
              in
           failwith uu____5801
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____5809) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta
           ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_unknown ;
              FStar_Syntax_Syntax.pos = uu____5850;
              FStar_Syntax_Syntax.vars = uu____5851;_},FStar_Syntax_Syntax.Meta_alien
            (obj,desc,ty))
           ->
           let tsym =
             let uu____5868 = varops.fresh "t"  in
             (uu____5868, FStar_SMTEncoding_Term.Term_sort)  in
           let t1 = FStar_SMTEncoding_Util.mkFreeV tsym  in
           let decl =
             let uu____5871 =
               let uu____5882 =
                 let uu____5885 = FStar_Util.format1 "alien term (%s)" desc
                    in
                 FStar_Pervasives_Native.Some uu____5885  in
               ((FStar_Pervasives_Native.fst tsym), [],
                 FStar_SMTEncoding_Term.Term_sort, uu____5882)
                in
             FStar_SMTEncoding_Term.DeclFun uu____5871  in
           (t1, [decl])
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____5893) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x  in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____5903 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name  in
           (uu____5903, [])
       | FStar_Syntax_Syntax.Tm_type uu____5906 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____5910) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c -> encode_const c env
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name  in
           let uu____5935 = FStar_Syntax_Subst.open_comp binders c  in
           (match uu____5935 with
            | (binders1,res) ->
                let uu____5946 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res)
                   in
                if uu____5946
                then
                  let uu____5951 =
                    encode_binders FStar_Pervasives_Native.None binders1 env
                     in
                  (match uu____5951 with
                   | (vars,guards,env',decls,uu____5976) ->
                       let fsym =
                         let uu____5994 = varops.fresh "f"  in
                         (uu____5994, FStar_SMTEncoding_Term.Term_sort)  in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                       let app = mk_Apply f vars  in
                       let uu____5997 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___109_6006 = env.tcenv  in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___109_6006.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___109_6006.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___109_6006.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___109_6006.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___109_6006.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___109_6006.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___109_6006.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___109_6006.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___109_6006.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___109_6006.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___109_6006.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___109_6006.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___109_6006.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___109_6006.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___109_6006.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___109_6006.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___109_6006.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___109_6006.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___109_6006.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.failhard =
                                (uu___109_6006.FStar_TypeChecker_Env.failhard);
                              FStar_TypeChecker_Env.nosynth =
                                (uu___109_6006.FStar_TypeChecker_Env.nosynth);
                              FStar_TypeChecker_Env.tc_term =
                                (uu___109_6006.FStar_TypeChecker_Env.tc_term);
                              FStar_TypeChecker_Env.type_of =
                                (uu___109_6006.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___109_6006.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___109_6006.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___109_6006.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___109_6006.FStar_TypeChecker_Env.proof_ns);
                              FStar_TypeChecker_Env.synth =
                                (uu___109_6006.FStar_TypeChecker_Env.synth);
                              FStar_TypeChecker_Env.is_native_tactic =
                                (uu___109_6006.FStar_TypeChecker_Env.is_native_tactic);
                              FStar_TypeChecker_Env.identifier_info =
                                (uu___109_6006.FStar_TypeChecker_Env.identifier_info);
                              FStar_TypeChecker_Env.tc_hooks =
                                (uu___109_6006.FStar_TypeChecker_Env.tc_hooks);
                              FStar_TypeChecker_Env.dsenv =
                                (uu___109_6006.FStar_TypeChecker_Env.dsenv);
                              FStar_TypeChecker_Env.dep_graph =
                                (uu___109_6006.FStar_TypeChecker_Env.dep_graph)
                            }) res
                          in
                       (match uu____5997 with
                        | (pre_opt,res_t) ->
                            let uu____6017 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app
                               in
                            (match uu____6017 with
                             | (res_pred,decls') ->
                                 let uu____6028 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____6041 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards
                                          in
                                       (uu____6041, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____6045 =
                                         encode_formula pre env'  in
                                       (match uu____6045 with
                                        | (guard,decls0) ->
                                            let uu____6058 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards)
                                               in
                                            (uu____6058, decls0))
                                    in
                                 (match uu____6028 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____6070 =
                                          let uu____6081 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred)
                                             in
                                          ([[app]], vars, uu____6081)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____6070
                                         in
                                      let cvars =
                                        let uu____6099 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp
                                           in
                                        FStar_All.pipe_right uu____6099
                                          (FStar_List.filter
                                             (fun uu____6113  ->
                                                match uu____6113 with
                                                | (x,uu____6119) ->
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
                                      let uu____6138 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____6138 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____6146 =
                                             let uu____6147 =
                                               let uu____6154 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV)
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____6154)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6147
                                              in
                                           (uu____6146,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____6174 =
                                               let uu____6175 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____6175
                                                in
                                             varops.mk_unique uu____6174  in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars
                                              in
                                           let caption =
                                             let uu____6186 =
                                               FStar_Options.log_queries ()
                                                in
                                             if uu____6186
                                             then
                                               let uu____6189 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6189
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
                                             let uu____6197 =
                                               let uu____6204 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars
                                                  in
                                               (tsym, uu____6204)  in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____6197
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
                                             let uu____6216 =
                                               let uu____6223 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind)
                                                  in
                                               (uu____6223,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name)
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6216
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
                                             let uu____6244 =
                                               let uu____6251 =
                                                 let uu____6252 =
                                                   let uu____6263 =
                                                     let uu____6264 =
                                                       let uu____6269 =
                                                         let uu____6270 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f
                                                            in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____6270
                                                          in
                                                       (f_has_t, uu____6269)
                                                        in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____6264
                                                      in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____6263)
                                                    in
                                                 mkForall_fuel uu____6252  in
                                               (uu____6251,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6244
                                              in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym
                                                in
                                             let uu____6293 =
                                               let uu____6300 =
                                                 let uu____6301 =
                                                   let uu____6312 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp)
                                                      in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____6312)
                                                    in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____6301
                                                  in
                                               (uu____6300,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name)))
                                                in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____6293
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
                                           ((let uu____6337 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls
                                                in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____6337);
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
                     let uu____6352 =
                       let uu____6359 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type
                          in
                       (uu____6359,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6352  in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort)  in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym  in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1  in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym  in
                     let uu____6371 =
                       let uu____6378 =
                         let uu____6379 =
                           let uu____6390 =
                             let uu____6391 =
                               let uu____6396 =
                                 let uu____6397 =
                                   FStar_SMTEncoding_Term.mk_PreType f  in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____6397
                                  in
                               (f_has_t, uu____6396)  in
                             FStar_SMTEncoding_Util.mkImp uu____6391  in
                           ([[f_has_t]], [fsym], uu____6390)  in
                         mkForall_fuel uu____6379  in
                       (uu____6378, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name)))
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____6371  in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____6424 ->
           let uu____6431 =
             let uu____6436 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.Weak;
                 FStar_TypeChecker_Normalize.HNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0
                in
             match uu____6436 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.pos = uu____6443;
                 FStar_Syntax_Syntax.vars = uu____6444;_} ->
                 let uu____6451 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f
                    in
                 (match uu____6451 with
                  | (b,f1) ->
                      let uu____6476 =
                        let uu____6477 = FStar_List.hd b  in
                        FStar_Pervasives_Native.fst uu____6477  in
                      (uu____6476, f1))
             | uu____6486 -> failwith "impossible"  in
           (match uu____6431 with
            | (x,f) ->
                let uu____6497 = encode_term x.FStar_Syntax_Syntax.sort env
                   in
                (match uu____6497 with
                 | (base_t,decls) ->
                     let uu____6508 = gen_term_var env x  in
                     (match uu____6508 with
                      | (x1,xtm,env') ->
                          let uu____6522 = encode_formula f env'  in
                          (match uu____6522 with
                           | (refinement,decls') ->
                               let uu____6533 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort
                                  in
                               (match uu____6533 with
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
                                      let uu____6549 =
                                        let uu____6552 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement
                                           in
                                        let uu____6559 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel
                                           in
                                        FStar_List.append uu____6552
                                          uu____6559
                                         in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____6549
                                       in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____6592  ->
                                              match uu____6592 with
                                              | (y,uu____6598) ->
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
                                    let uu____6631 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash
                                       in
                                    (match uu____6631 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____6639 =
                                           let uu____6640 =
                                             let uu____6647 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV)
                                                in
                                             ((cache_entry.cache_symbol_name),
                                               uu____6647)
                                              in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6640
                                            in
                                         (uu____6639,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name  in
                                         let tsym =
                                           let uu____6668 =
                                             let uu____6669 =
                                               let uu____6670 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash
                                                  in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____6670
                                                in
                                             Prims.strcat module_name
                                               uu____6669
                                              in
                                           varops.mk_unique uu____6668  in
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
                                           let uu____6684 =
                                             let uu____6691 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1
                                                in
                                             (tsym, uu____6691)  in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____6684
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
                                           let uu____6706 =
                                             let uu____6713 =
                                               let uu____6714 =
                                                 let uu____6725 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base)
                                                    in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____6725)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6714
                                                in
                                             (uu____6713,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6706
                                            in
                                         let t_kinding =
                                           let uu____6743 =
                                             let uu____6750 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind)
                                                in
                                             (uu____6750,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6743
                                            in
                                         let t_interp =
                                           let uu____6768 =
                                             let uu____6775 =
                                               let uu____6776 =
                                                 let uu____6787 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding)
                                                    in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____6787)
                                                  in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____6776
                                                in
                                             let uu____6810 =
                                               let uu____6813 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0
                                                  in
                                               FStar_Pervasives_Native.Some
                                                 uu____6813
                                                in
                                             (uu____6775, uu____6810,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym))
                                              in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____6768
                                            in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1])
                                            in
                                         ((let uu____6820 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls
                                              in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____6820);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____6850 = FStar_Syntax_Unionfind.uvar_id uv  in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____6850  in
           let uu____6851 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm  in
           (match uu____6851 with
            | (t_has_k,decls) ->
                let d =
                  let uu____6863 =
                    let uu____6870 =
                      let uu____6871 =
                        let uu____6872 =
                          let uu____6873 = FStar_Syntax_Unionfind.uvar_id uv
                             in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____6873
                           in
                        FStar_Util.format1 "uvar_typing_%s" uu____6872  in
                      varops.mk_unique uu____6871  in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____6870)
                     in
                  FStar_SMTEncoding_Util.mkAssume uu____6863  in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____6878 ->
           let uu____6893 = FStar_Syntax_Util.head_and_args t0  in
           (match uu____6893 with
            | (head1,args_e) ->
                let uu____6934 =
                  let uu____6947 =
                    let uu____6948 = FStar_Syntax_Subst.compress head1  in
                    uu____6948.FStar_Syntax_Syntax.n  in
                  (uu____6947, args_e)  in
                (match uu____6934 with
                 | uu____6963 when head_redex env head1 ->
                     let uu____6976 = whnf env t  in
                     encode_term uu____6976 env
                 | uu____6977 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | uu____6996 when is_BitVector_primitive head1 args_e ->
                     encode_BitVector_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.pos = uu____7010;
                       FStar_Syntax_Syntax.vars = uu____7011;_},uu____7012),uu____7013::
                    (v1,uu____7015)::(v2,uu____7017)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7068 = encode_term v1 env  in
                     (match uu____7068 with
                      | (v11,decls1) ->
                          let uu____7079 = encode_term v2 env  in
                          (match uu____7079 with
                           | (v21,decls2) ->
                               let uu____7090 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7090,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____7094::(v1,uu____7096)::(v2,uu____7098)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____7145 = encode_term v1 env  in
                     (match uu____7145 with
                      | (v11,decls1) ->
                          let uu____7156 = encode_term v2 env  in
                          (match uu____7156 with
                           | (v21,decls2) ->
                               let uu____7167 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21
                                  in
                               (uu____7167,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_range_of ),(arg,uu____7171)::[]) ->
                     encode_const
                       (FStar_Const.Const_range (arg.FStar_Syntax_Syntax.pos))
                       env
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_set_range_of
                    ),(arg,uu____7197)::(rng,uu____7199)::[]) ->
                     encode_term arg env
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____7234) ->
                     let e0 =
                       let uu____7252 = FStar_List.hd args_e  in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____7252
                        in
                     ((let uu____7260 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify")
                          in
                       if uu____7260
                       then
                         let uu____7261 =
                           FStar_Syntax_Print.term_to_string e0  in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____7261
                       else ());
                      (let e =
                         let uu____7266 =
                           let uu____7267 =
                             FStar_TypeChecker_Util.remove_reify e0  in
                           let uu____7268 = FStar_List.tl args_e  in
                           FStar_Syntax_Syntax.mk_Tm_app uu____7267
                             uu____7268
                            in
                         uu____7266 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos
                          in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____7277),(arg,uu____7279)::[]) -> encode_term arg env
                 | uu____7304 ->
                     let uu____7317 = encode_args args_e env  in
                     (match uu____7317 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____7372 = encode_term head1 env  in
                            match uu____7372 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args  in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____7436 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals
                                        in
                                     (match uu____7436 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____7514  ->
                                                 fun uu____7515  ->
                                                   match (uu____7514,
                                                           uu____7515)
                                                   with
                                                   | ((bv,uu____7537),
                                                      (a,uu____7539)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e
                                             in
                                          let ty =
                                            let uu____7557 =
                                              FStar_Syntax_Util.arrow rest c
                                               in
                                            FStar_All.pipe_right uu____7557
                                              (FStar_Syntax_Subst.subst
                                                 subst1)
                                             in
                                          let uu____7562 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm
                                             in
                                          (match uu____7562 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type
                                                  in
                                               let e_typing =
                                                 let uu____7577 =
                                                   let uu____7584 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type)
                                                      in
                                                   let uu____7593 =
                                                     let uu____7594 =
                                                       let uu____7595 =
                                                         let uu____7596 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm
                                                            in
                                                         FStar_Util.digest_of_string
                                                           uu____7596
                                                          in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____7595
                                                        in
                                                     varops.mk_unique
                                                       uu____7594
                                                      in
                                                   (uu____7584,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____7593)
                                                    in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____7577
                                                  in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing])))))))
                             in
                          let encode_full_app fv =
                            let uu____7613 = lookup_free_var_sym env fv  in
                            match uu____7613 with
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
                                   FStar_Syntax_Syntax.pos = uu____7644;
                                   FStar_Syntax_Syntax.vars = uu____7645;_},uu____7646)
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
                                   FStar_Syntax_Syntax.pos = uu____7657;
                                   FStar_Syntax_Syntax.vars = uu____7658;_},uu____7659)
                                ->
                                let uu____7664 =
                                  let uu____7665 =
                                    let uu____7670 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7670
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7665
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7664
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____7700 =
                                  let uu____7701 =
                                    let uu____7706 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                       in
                                    FStar_All.pipe_right uu____7706
                                      FStar_Pervasives_Native.fst
                                     in
                                  FStar_All.pipe_right uu____7701
                                    FStar_Pervasives_Native.snd
                                   in
                                FStar_Pervasives_Native.Some uu____7700
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7735,(FStar_Util.Inl t1,uu____7737),uu____7738)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____7787,(FStar_Util.Inr c,uu____7789),uu____7790)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____7839 -> FStar_Pervasives_Native.None  in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____7866 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.Weak;
                                     FStar_TypeChecker_Normalize.HNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1
                                    in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____7866
                                  in
                               let uu____7867 =
                                 curried_arrow_formals_comp head_type2  in
                               (match uu____7867 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.pos =
                                              uu____7883;
                                            FStar_Syntax_Syntax.vars =
                                              uu____7884;_},uu____7885)
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
                                     | uu____7899 ->
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
           let uu____7948 = FStar_Syntax_Subst.open_term' bs body  in
           (match uu____7948 with
            | (bs1,body1,opening) ->
                let fallback uu____7971 =
                  let f = varops.fresh "Tm_abs"  in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding"))
                     in
                  let uu____7978 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort)
                     in
                  (uu____7978, [decl])  in
                let is_impure rc =
                  let uu____7985 =
                    FStar_TypeChecker_Util.is_pure_or_ghost_effect env.tcenv
                      rc.FStar_Syntax_Syntax.residual_effect
                     in
                  FStar_All.pipe_right uu____7985 Prims.op_Negation  in
                let codomain_eff rc =
                  let res_typ =
                    match rc.FStar_Syntax_Syntax.residual_typ with
                    | FStar_Pervasives_Native.None  ->
                        let uu____7995 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0
                           in
                        FStar_All.pipe_right uu____7995
                          FStar_Pervasives_Native.fst
                    | FStar_Pervasives_Native.Some t1 -> t1  in
                  if
                    FStar_Ident.lid_equals
                      rc.FStar_Syntax_Syntax.residual_effect
                      FStar_Parser_Const.effect_Tot_lid
                  then
                    let uu____8015 = FStar_Syntax_Syntax.mk_Total res_typ  in
                    FStar_Pervasives_Native.Some uu____8015
                  else
                    if
                      FStar_Ident.lid_equals
                        rc.FStar_Syntax_Syntax.residual_effect
                        FStar_Parser_Const.effect_GTot_lid
                    then
                      (let uu____8019 = FStar_Syntax_Syntax.mk_GTotal res_typ
                          in
                       FStar_Pervasives_Native.Some uu____8019)
                    else FStar_Pervasives_Native.None
                   in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____8026 =
                         let uu____8031 =
                           let uu____8032 =
                             FStar_Syntax_Print.term_to_string t0  in
                           FStar_Util.format1
                             "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                             uu____8032
                            in
                         (FStar_Errors.Warning_FunctionLiteralPrecisionLoss,
                           uu____8031)
                          in
                       FStar_Errors.log_issue t0.FStar_Syntax_Syntax.pos
                         uu____8026);
                      fallback ())
                 | FStar_Pervasives_Native.Some rc ->
                     let uu____8034 =
                       (is_impure rc) &&
                         (let uu____8036 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv rc
                             in
                          Prims.op_Negation uu____8036)
                        in
                     if uu____8034
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache  in
                        let uu____8043 =
                          encode_binders FStar_Pervasives_Native.None bs1 env
                           in
                        match uu____8043 with
                        | (vars,guards,envbody,decls,uu____8068) ->
                            let body2 =
                              let uu____8082 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  rc
                                 in
                              if uu____8082
                              then
                                FStar_TypeChecker_Util.reify_body env.tcenv
                                  body1
                              else body1  in
                            let uu____8084 = encode_term body2 envbody  in
                            (match uu____8084 with
                             | (body3,decls') ->
                                 let uu____8095 =
                                   let uu____8104 = codomain_eff rc  in
                                   match uu____8104 with
                                   | FStar_Pervasives_Native.None  ->
                                       (FStar_Pervasives_Native.None, [])
                                   | FStar_Pervasives_Native.Some c ->
                                       let tfun =
                                         FStar_Syntax_Util.arrow bs1 c  in
                                       let uu____8123 = encode_term tfun env
                                          in
                                       (match uu____8123 with
                                        | (t1,decls1) ->
                                            ((FStar_Pervasives_Native.Some t1),
                                              decls1))
                                    in
                                 (match uu____8095 with
                                  | (arrow_t_opt,decls'') ->
                                      let key_body =
                                        let uu____8155 =
                                          let uu____8166 =
                                            let uu____8167 =
                                              let uu____8172 =
                                                FStar_SMTEncoding_Util.mk_and_l
                                                  guards
                                                 in
                                              (uu____8172, body3)  in
                                            FStar_SMTEncoding_Util.mkImp
                                              uu____8167
                                             in
                                          ([], vars, uu____8166)  in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____8155
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
                                            let uu____8184 =
                                              let uu____8187 =
                                                FStar_SMTEncoding_Term.free_variables
                                                  t1
                                                 in
                                              FStar_List.append uu____8187
                                                cvars
                                               in
                                            FStar_Util.remove_dups
                                              FStar_SMTEncoding_Term.fv_eq
                                              uu____8184
                                         in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], cvars1, key_body)
                                         in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey
                                         in
                                      let uu____8206 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash
                                         in
                                      (match uu____8206 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____8214 =
                                             let uu____8215 =
                                               let uu____8222 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars1
                                                  in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____8222)
                                                in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____8215
                                              in
                                           (uu____8214,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append decls''
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let uu____8233 =
                                             is_an_eta_expansion env vars
                                               body3
                                              in
                                           (match uu____8233 with
                                            | FStar_Pervasives_Native.Some t1
                                                ->
                                                let decls1 =
                                                  let uu____8244 =
                                                    let uu____8245 =
                                                      FStar_Util.smap_size
                                                        env.cache
                                                       in
                                                    uu____8245 = cache_size
                                                     in
                                                  if uu____8244
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
                                                    let uu____8261 =
                                                      let uu____8262 =
                                                        FStar_Util.digest_of_string
                                                          tkey_hash
                                                         in
                                                      Prims.strcat "Tm_abs_"
                                                        uu____8262
                                                       in
                                                    varops.mk_unique
                                                      uu____8261
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
                                                  let uu____8269 =
                                                    let uu____8276 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1
                                                       in
                                                    (fsym, uu____8276)  in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____8269
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
                                                      let uu____8294 =
                                                        let uu____8295 =
                                                          let uu____8302 =
                                                            FStar_SMTEncoding_Util.mkForall
                                                              ([[f]], cvars1,
                                                                f_has_t)
                                                             in
                                                          (uu____8302,
                                                            (FStar_Pervasives_Native.Some
                                                               a_name),
                                                            a_name)
                                                           in
                                                        FStar_SMTEncoding_Util.mkAssume
                                                          uu____8295
                                                         in
                                                      [uu____8294]
                                                   in
                                                let interp_f =
                                                  let a_name =
                                                    Prims.strcat
                                                      "interpretation_" fsym
                                                     in
                                                  let uu____8315 =
                                                    let uu____8322 =
                                                      let uu____8323 =
                                                        let uu____8334 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (app, body3)
                                                           in
                                                        ([[app]],
                                                          (FStar_List.append
                                                             vars cvars1),
                                                          uu____8334)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____8323
                                                       in
                                                    (uu____8322,
                                                      (FStar_Pervasives_Native.Some
                                                         a_name), a_name)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____8315
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
                                                ((let uu____8351 =
                                                    mk_cache_entry env fsym
                                                      cvar_sorts f_decls
                                                     in
                                                  FStar_Util.smap_add
                                                    env.cache tkey_hash
                                                    uu____8351);
                                                 (f, f_decls)))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____8354,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____8355;
                          FStar_Syntax_Syntax.lbunivs = uu____8356;
                          FStar_Syntax_Syntax.lbtyp = uu____8357;
                          FStar_Syntax_Syntax.lbeff = uu____8358;
                          FStar_Syntax_Syntax.lbdef = uu____8359;_}::uu____8360),uu____8361)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____8387;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____8389;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____8410 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions, and their enclosings let bindings (including the top-level let) are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            FStar_Exn.raise Inner_let_rec)
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)

and (encode_let :
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
                FStar_Pervasives_Native.tuple2)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____8480 = encode_term e1 env  in
              match uu____8480 with
              | (ee1,decls1) ->
                  let uu____8491 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2
                     in
                  (match uu____8491 with
                   | (xs,e21) ->
                       let uu____8516 = FStar_List.hd xs  in
                       (match uu____8516 with
                        | (x1,uu____8530) ->
                            let env' = push_term_var env x1 ee1  in
                            let uu____8532 = encode_body e21 env'  in
                            (match uu____8532 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))

and (encode_match :
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
              FStar_Pervasives_Native.tuple2)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____8564 =
              let uu____8571 =
                let uu____8572 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange
                   in
                FStar_Syntax_Syntax.null_bv uu____8572  in
              gen_term_var env uu____8571  in
            match uu____8564 with
            | (scrsym,scr',env1) ->
                let uu____8580 = encode_term e env1  in
                (match uu____8580 with
                 | (scr,decls) ->
                     let uu____8591 =
                       let encode_branch b uu____8616 =
                         match uu____8616 with
                         | (else_case,decls1) ->
                             let uu____8635 =
                               FStar_Syntax_Subst.open_branch b  in
                             (match uu____8635 with
                              | (p,w,br) ->
                                  let uu____8661 = encode_pat env1 p  in
                                  (match uu____8661 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr'  in
                                       let projections =
                                         pattern.projections scr'  in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____8698  ->
                                                   match uu____8698 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1)
                                          in
                                       let uu____8705 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____8727 =
                                               encode_term w1 env2  in
                                             (match uu____8727 with
                                              | (w2,decls2) ->
                                                  let uu____8740 =
                                                    let uu____8741 =
                                                      let uu____8746 =
                                                        let uu____8747 =
                                                          let uu____8752 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue
                                                             in
                                                          (w2, uu____8752)
                                                           in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____8747
                                                         in
                                                      (guard, uu____8746)  in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____8741
                                                     in
                                                  (uu____8740, decls2))
                                          in
                                       (match uu____8705 with
                                        | (guard1,decls2) ->
                                            let uu____8765 =
                                              encode_br br env2  in
                                            (match uu____8765 with
                                             | (br1,decls3) ->
                                                 let uu____8778 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case)
                                                    in
                                                 (uu____8778,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3)))))))
                          in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls)
                        in
                     (match uu____8591 with
                      | (match_tm,decls1) ->
                          let uu____8797 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange
                             in
                          (uu____8797, decls1)))

and (encode_pat :
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun pat  ->
      (let uu____8837 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low  in
       if uu____8837
       then
         let uu____8838 = FStar_Syntax_Print.pat_to_string pat  in
         FStar_Util.print1 "Encoding pattern %s\n" uu____8838
       else ());
      (let uu____8840 = FStar_TypeChecker_Util.decorated_pattern_as_term pat
          in
       match uu____8840 with
       | (vars,pat_term) ->
           let uu____8857 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____8910  ->
                     fun v1  ->
                       match uu____8910 with
                       | (env1,vars1) ->
                           let uu____8962 = gen_term_var env1 v1  in
                           (match uu____8962 with
                            | (xx,uu____8984,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, []))
              in
           (match uu____8857 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____9063 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____9064 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____9065 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____9073 = encode_const c env1  in
                      (match uu____9073 with
                       | (tm,decls) ->
                           ((match decls with
                             | uu____9087::uu____9088 ->
                                 failwith
                                   "Unexpected encoding of constant pattern"
                             | uu____9091 -> ());
                            FStar_SMTEncoding_Util.mkEq (scrutinee, tm)))
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                           in
                        let uu____9114 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name
                           in
                        match uu____9114 with
                        | (uu____9121,uu____9122::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____9125 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee
                         in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9158  ->
                                  match uu____9158 with
                                  | (arg,uu____9166) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9172 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_guard arg uu____9172))
                         in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards)
                   in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____9199) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____9230 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____9253 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____9297  ->
                                  match uu____9297 with
                                  | (arg,uu____9311) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i
                                         in
                                      let uu____9317 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee])
                                         in
                                      mk_projections arg uu____9317))
                         in
                      FStar_All.pipe_right uu____9253 FStar_List.flatten
                   in
                let pat_term1 uu____9345 = encode_term pat_term env1  in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  }  in
                (env1, pattern)))

and (encode_args :
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun l  ->
    fun env  ->
      let uu____9355 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____9393  ->
                fun uu____9394  ->
                  match (uu____9393, uu____9394) with
                  | ((tms,decls),(t,uu____9430)) ->
                      let uu____9451 = encode_term t env  in
                      (match uu____9451 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], []))
         in
      match uu____9355 with | (l1,decls) -> ((FStar_List.rev l1), decls)

and (encode_function_type_as_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____9508 = FStar_Syntax_Util.list_elements e  in
        match uu____9508 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.log_issue e.FStar_Syntax_Syntax.pos
               (FStar_Errors.Warning_NonListLiteralSMTPattern,
                 "SMT pattern is not a list literal; ignoring the pattern");
             [])
         in
      let one_pat p =
        let uu____9529 =
          let uu____9544 = FStar_Syntax_Util.unmeta p  in
          FStar_All.pipe_right uu____9544 FStar_Syntax_Util.head_and_args  in
        match uu____9529 with
        | (head1,args) ->
            let uu____9583 =
              let uu____9596 =
                let uu____9597 = FStar_Syntax_Util.un_uinst head1  in
                uu____9597.FStar_Syntax_Syntax.n  in
              (uu____9596, args)  in
            (match uu____9583 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____9611,uu____9612)::(e,uu____9614)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | uu____9649 -> failwith "Unexpected pattern term")
         in
      let lemma_pats p =
        let elts = list_elements1 p  in
        let smt_pat_or1 t1 =
          let uu____9685 =
            let uu____9700 = FStar_Syntax_Util.unmeta t1  in
            FStar_All.pipe_right uu____9700 FStar_Syntax_Util.head_and_args
             in
          match uu____9685 with
          | (head1,args) ->
              let uu____9741 =
                let uu____9754 =
                  let uu____9755 = FStar_Syntax_Util.un_uinst head1  in
                  uu____9755.FStar_Syntax_Syntax.n  in
                (uu____9754, args)  in
              (match uu____9741 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____9772)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____9799 -> FStar_Pervasives_Native.None)
           in
        match elts with
        | t1::[] ->
            let uu____9821 = smt_pat_or1 t1  in
            (match uu____9821 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____9837 = list_elements1 e  in
                 FStar_All.pipe_right uu____9837
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____9855 = list_elements1 branch1  in
                         FStar_All.pipe_right uu____9855
                           (FStar_List.map one_pat)))
             | uu____9866 ->
                 let uu____9871 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat)  in
                 [uu____9871])
        | uu____9892 ->
            let uu____9895 =
              FStar_All.pipe_right elts (FStar_List.map one_pat)  in
            [uu____9895]
         in
      let uu____9916 =
        let uu____9935 =
          let uu____9936 = FStar_Syntax_Subst.compress t  in
          uu____9936.FStar_Syntax_Syntax.n  in
        match uu____9935 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____9975 = FStar_Syntax_Subst.open_comp binders c  in
            (match uu____9975 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____10018;
                        FStar_Syntax_Syntax.effect_name = uu____10019;
                        FStar_Syntax_Syntax.result_typ = uu____10020;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____10022)::(post,uu____10024)::(pats,uu____10026)::[];
                        FStar_Syntax_Syntax.flags = uu____10027;_}
                      ->
                      let uu____10068 = lemma_pats pats  in
                      (binders1, pre, post, uu____10068)
                  | uu____10085 -> failwith "impos"))
        | uu____10104 -> failwith "Impos"  in
      match uu____9916 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___110_10152 = env  in
            {
              bindings = (uu___110_10152.bindings);
              depth = (uu___110_10152.depth);
              tcenv = (uu___110_10152.tcenv);
              warn = (uu___110_10152.warn);
              cache = (uu___110_10152.cache);
              nolabels = (uu___110_10152.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___110_10152.encode_non_total_function_typ);
              current_module_name = (uu___110_10152.current_module_name)
            }  in
          let uu____10153 =
            encode_binders FStar_Pervasives_Native.None binders env1  in
          (match uu____10153 with
           | (vars,guards,env2,decls,uu____10178) ->
               let uu____10191 =
                 let uu____10206 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____10260 =
                             let uu____10271 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_smt_pattern t1 env2))
                                in
                             FStar_All.pipe_right uu____10271
                               FStar_List.unzip
                              in
                           match uu____10260 with
                           | (pats,decls1) -> (pats, decls1)))
                    in
                 FStar_All.pipe_right uu____10206 FStar_List.unzip  in
               (match uu____10191 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls'  in
                    let post1 = FStar_Syntax_Util.unthunk_lemma_post post  in
                    let env3 =
                      let uu___111_10423 = env2  in
                      {
                        bindings = (uu___111_10423.bindings);
                        depth = (uu___111_10423.depth);
                        tcenv = (uu___111_10423.tcenv);
                        warn = (uu___111_10423.warn);
                        cache = (uu___111_10423.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___111_10423.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___111_10423.encode_non_total_function_typ);
                        current_module_name =
                          (uu___111_10423.current_module_name)
                      }  in
                    let uu____10424 =
                      let uu____10429 = FStar_Syntax_Util.unmeta pre  in
                      encode_formula uu____10429 env3  in
                    (match uu____10424 with
                     | (pre1,decls'') ->
                         let uu____10436 =
                           let uu____10441 = FStar_Syntax_Util.unmeta post1
                              in
                           encode_formula uu____10441 env3  in
                         (match uu____10436 with
                          | (post2,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls'''))
                                 in
                              let uu____10451 =
                                let uu____10452 =
                                  let uu____10463 =
                                    let uu____10464 =
                                      let uu____10469 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards)
                                         in
                                      (uu____10469, post2)  in
                                    FStar_SMTEncoding_Util.mkImp uu____10464
                                     in
                                  (pats, vars, uu____10463)  in
                                FStar_SMTEncoding_Util.mkForall uu____10452
                                 in
                              (uu____10451, decls1)))))

and (encode_smt_pattern :
  FStar_Syntax_Syntax.term' FStar_Syntax_Syntax.syntax ->
    env_t ->
      (FStar_SMTEncoding_Term.pat,FStar_SMTEncoding_Term.decl Prims.list)
        FStar_Pervasives_Native.tuple2)
  =
  fun t  ->
    fun env  ->
      let uu____10482 = FStar_Syntax_Util.head_and_args t  in
      match uu____10482 with
      | (head1,args) ->
          let head2 = FStar_Syntax_Util.un_uinst head1  in
          (match ((head2.FStar_Syntax_Syntax.n), args) with
           | (FStar_Syntax_Syntax.Tm_fvar
              fv,uu____10541::(x,uu____10543)::(t1,uu____10545)::[]) when
               FStar_Syntax_Syntax.fv_eq_lid fv
                 FStar_Parser_Const.has_type_lid
               ->
               let uu____10592 = encode_term x env  in
               (match uu____10592 with
                | (x1,decls) ->
                    let uu____10605 = encode_term t1 env  in
                    (match uu____10605 with
                     | (t2,decls') ->
                         let uu____10618 =
                           FStar_SMTEncoding_Term.mk_HasType x1 t2  in
                         (uu____10618, (FStar_List.append decls decls'))))
           | uu____10621 -> encode_term t env)

and (encode_formula :
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____10644 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding")
           in
        if uu____10644
        then
          let uu____10645 = FStar_Syntax_Print.tag_of_term phi1  in
          let uu____10646 = FStar_Syntax_Print.term_to_string phi1  in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____10645 uu____10646
        else ()  in
      let enc f r l =
        let uu____10679 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____10707 =
                   encode_term (FStar_Pervasives_Native.fst x) env  in
                 match uu____10707 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l
           in
        match uu____10679 with
        | (decls,args) ->
            let uu____10736 =
              let uu___112_10737 = f args  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___112_10737.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___112_10737.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10736, decls)
         in
      let const_op f r uu____10768 =
        let uu____10781 = f r  in (uu____10781, [])  in
      let un_op f l =
        let uu____10800 = FStar_List.hd l  in
        FStar_All.pipe_left f uu____10800  in
      let bin_op f uu___86_10816 =
        match uu___86_10816 with
        | t1::t2::[] -> f (t1, t2)
        | uu____10827 -> failwith "Impossible"  in
      let enc_prop_c f r l =
        let uu____10861 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____10884  ->
                 match uu____10884 with
                 | (t,uu____10898) ->
                     let uu____10899 = encode_formula t env  in
                     (match uu____10899 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l
           in
        match uu____10861 with
        | (decls,phis) ->
            let uu____10928 =
              let uu___113_10929 = f phis  in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___113_10929.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___113_10929.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              }  in
            (uu____10928, decls)
         in
      let eq_op r args =
        let rf =
          FStar_List.filter
            (fun uu____10990  ->
               match uu____10990 with
               | (a,q) ->
                   (match q with
                    | FStar_Pervasives_Native.Some
                        (FStar_Syntax_Syntax.Implicit uu____11009) -> false
                    | uu____11010 -> true)) args
           in
        if (FStar_List.length rf) <> (Prims.parse_int "2")
        then
          let uu____11025 =
            FStar_Util.format1
              "eq_op: got %s non-implicit arguments instead of 2?"
              (Prims.string_of_int (FStar_List.length rf))
             in
          failwith uu____11025
        else
          (let uu____11039 = enc (bin_op FStar_SMTEncoding_Util.mkEq)  in
           uu____11039 r rf)
         in
      let mk_imp1 r uu___87_11064 =
        match uu___87_11064 with
        | (lhs,uu____11070)::(rhs,uu____11072)::[] ->
            let uu____11099 = encode_formula rhs env  in
            (match uu____11099 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____11114) ->
                      (l1, decls1)
                  | uu____11119 ->
                      let uu____11120 = encode_formula lhs env  in
                      (match uu____11120 with
                       | (l2,decls2) ->
                           let uu____11131 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r  in
                           (uu____11131, (FStar_List.append decls1 decls2)))))
        | uu____11134 -> failwith "impossible"  in
      let mk_ite r uu___88_11155 =
        match uu___88_11155 with
        | (guard,uu____11161)::(_then,uu____11163)::(_else,uu____11165)::[]
            ->
            let uu____11202 = encode_formula guard env  in
            (match uu____11202 with
             | (g,decls1) ->
                 let uu____11213 = encode_formula _then env  in
                 (match uu____11213 with
                  | (t,decls2) ->
                      let uu____11224 = encode_formula _else env  in
                      (match uu____11224 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r
                              in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____11238 -> failwith "impossible"  in
      let unboxInt_l f l =
        let uu____11263 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l
           in
        f uu____11263  in
      let connectives =
        let uu____11281 =
          let uu____11294 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd)
             in
          (FStar_Parser_Const.and_lid, uu____11294)  in
        let uu____11311 =
          let uu____11326 =
            let uu____11339 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr)
               in
            (FStar_Parser_Const.or_lid, uu____11339)  in
          let uu____11356 =
            let uu____11371 =
              let uu____11386 =
                let uu____11399 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff)  in
                (FStar_Parser_Const.iff_lid, uu____11399)  in
              let uu____11416 =
                let uu____11431 =
                  let uu____11446 =
                    let uu____11459 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot)  in
                    (FStar_Parser_Const.not_lid, uu____11459)  in
                  [uu____11446;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))]
                   in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____11431  in
              uu____11386 :: uu____11416  in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____11371  in
          uu____11326 :: uu____11356  in
        uu____11281 :: uu____11311  in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____11780 = encode_formula phi' env  in
            (match uu____11780 with
             | (phi2,decls) ->
                 let uu____11791 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r
                    in
                 (uu____11791, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____11792 ->
            let uu____11799 = FStar_Syntax_Util.unmeta phi1  in
            encode_formula uu____11799 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____11838 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula
               in
            (match uu____11838 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____11850;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____11852;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____11873 = encode_let x t1 e1 e2 env encode_formula  in
            (match uu____11873 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1  in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____11920::(x,uu____11922)::(t,uu____11924)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____11971 = encode_term x env  in
                 (match uu____11971 with
                  | (x1,decls) ->
                      let uu____11982 = encode_term t env  in
                      (match uu____11982 with
                       | (t1,decls') ->
                           let uu____11993 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1  in
                           (uu____11993, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____11998)::(msg,uu____12000)::(phi2,uu____12002)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____12047 =
                   let uu____12052 =
                     let uu____12053 = FStar_Syntax_Subst.compress r  in
                     uu____12053.FStar_Syntax_Syntax.n  in
                   let uu____12056 =
                     let uu____12057 = FStar_Syntax_Subst.compress msg  in
                     uu____12057.FStar_Syntax_Syntax.n  in
                   (uu____12052, uu____12056)  in
                 (match uu____12047 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____12066))) ->
                      let phi3 =
                        FStar_Syntax_Syntax.mk
                          (FStar_Syntax_Syntax.Tm_meta
                             (phi2,
                               (FStar_Syntax_Syntax.Meta_labeled
                                  (s, r1, false))))
                          FStar_Pervasives_Native.None r1
                         in
                      fallback phi3
                  | uu____12072 -> fallback phi2)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(t,uu____12079)::[]) when
                 (FStar_Syntax_Syntax.fv_eq_lid fv
                    FStar_Parser_Const.squash_lid)
                   ||
                   (FStar_Syntax_Syntax.fv_eq_lid fv
                      FStar_Parser_Const.auto_squash_lid)
                 -> encode_formula t env
             | uu____12104 when head_redex env head2 ->
                 let uu____12117 = whnf env phi1  in
                 encode_formula uu____12117 env
             | uu____12118 ->
                 let uu____12131 = encode_term phi1 env  in
                 (match uu____12131 with
                  | (tt,decls) ->
                      let uu____12142 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___114_12145 = tt  in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___114_12145.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___114_12145.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           })
                         in
                      (uu____12142, decls)))
        | uu____12146 ->
            let uu____12147 = encode_term phi1 env  in
            (match uu____12147 with
             | (tt,decls) ->
                 let uu____12158 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___115_12161 = tt  in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___115_12161.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___115_12161.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      })
                    in
                 (uu____12158, decls))
         in
      let encode_q_body env1 bs ps body =
        let uu____12197 = encode_binders FStar_Pervasives_Native.None bs env1
           in
        match uu____12197 with
        | (vars,guards,env2,decls,uu____12236) ->
            let uu____12249 =
              let uu____12262 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____12314 =
                          let uu____12325 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____12365  ->
                                    match uu____12365 with
                                    | (t,uu____12379) ->
                                        encode_smt_pattern t
                                          (let uu___116_12385 = env2  in
                                           {
                                             bindings =
                                               (uu___116_12385.bindings);
                                             depth = (uu___116_12385.depth);
                                             tcenv = (uu___116_12385.tcenv);
                                             warn = (uu___116_12385.warn);
                                             cache = (uu___116_12385.cache);
                                             nolabels =
                                               (uu___116_12385.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___116_12385.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___116_12385.current_module_name)
                                           })))
                             in
                          FStar_All.pipe_right uu____12325 FStar_List.unzip
                           in
                        match uu____12314 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1))))
                 in
              FStar_All.pipe_right uu____12262 FStar_List.unzip  in
            (match uu____12249 with
             | (pats,decls') ->
                 let uu____12494 = encode_formula body env2  in
                 (match uu____12494 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____12526;
                             FStar_SMTEncoding_Term.rng = uu____12527;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____12542 -> guards  in
                      let uu____12547 =
                        FStar_SMTEncoding_Util.mk_and_l guards1  in
                      (vars, pats, uu____12547, body1,
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
                (fun uu____12607  ->
                   match uu____12607 with
                   | (x,uu____12613) ->
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
               let uu____12621 = FStar_Syntax_Free.names hd1  in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____12633 = FStar_Syntax_Free.names x  in
                      FStar_Util.set_union out uu____12633) uu____12621 tl1
                in
             let uu____12636 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____12663  ->
                       match uu____12663 with
                       | (b,uu____12669) ->
                           let uu____12670 = FStar_Util.set_mem b pat_vars
                              in
                           Prims.op_Negation uu____12670))
                in
             (match uu____12636 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____12676) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1
                     in
                  let uu____12690 =
                    let uu____12695 =
                      let uu____12696 = FStar_Syntax_Print.bv_to_string x  in
                      FStar_Util.format1
                        "SMT pattern misses at least one bound variable: %s"
                        uu____12696
                       in
                    (FStar_Errors.Warning_SMTPatternMissingBoundVar,
                      uu____12695)
                     in
                  FStar_Errors.log_issue pos uu____12690)
          in
       let uu____12697 = FStar_Syntax_Util.destruct_typ_as_formula phi1  in
       match uu____12697 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____12706 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____12764  ->
                     match uu____12764 with
                     | (l,uu____12778) -> FStar_Ident.lid_equals op l))
              in
           (match uu____12706 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____12811,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12851 = encode_q_body env vars pats body  in
             match uu____12851 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____12896 =
                     let uu____12907 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1)  in
                     (pats1, vars1, uu____12907)  in
                   FStar_SMTEncoding_Term.mkForall uu____12896
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____12926 = encode_q_body env vars pats body  in
             match uu____12926 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____12970 =
                   let uu____12971 =
                     let uu____12982 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1)  in
                     (pats1, vars1, uu____12982)  in
                   FStar_SMTEncoding_Term.mkExists uu____12971
                     phi1.FStar_Syntax_Syntax.pos
                    in
                 (uu____12970, decls))))

type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2
    ;
  is: FStar_Ident.lident -> Prims.bool }[@@deriving show]
let (__proj__Mkprims_t__item__mk :
  prims_t ->
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2)
  =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__mk
  
let (__proj__Mkprims_t__item__is :
  prims_t -> FStar_Ident.lident -> Prims.bool) =
  fun projectee  ->
    match projectee with
    | { mk = __fname__mk; is = __fname__is;_} -> __fname__is
  
let (prims : prims_t) =
  let uu____13075 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort  in
  match uu____13075 with
  | (asym,a) ->
      let uu____13082 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
      (match uu____13082 with
       | (xsym,x) ->
           let uu____13089 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort
              in
           (match uu____13089 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____13133 =
                      let uu____13144 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd)
                         in
                      (x1, uu____13144, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____13133  in
                  let xtok = Prims.strcat x1 "@tok"  in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                     in
                  let xapp =
                    let uu____13170 =
                      let uu____13177 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars
                         in
                      (x1, uu____13177)  in
                    FStar_SMTEncoding_Util.mkApp uu____13170  in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, [])  in
                  let xtok_app = mk_Apply xtok1 vars  in
                  let uu____13190 =
                    let uu____13193 =
                      let uu____13196 =
                        let uu____13199 =
                          let uu____13200 =
                            let uu____13207 =
                              let uu____13208 =
                                let uu____13219 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body)
                                   in
                                ([[xapp]], vars, uu____13219)  in
                              FStar_SMTEncoding_Util.mkForall uu____13208  in
                            (uu____13207, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1))
                             in
                          FStar_SMTEncoding_Util.mkAssume uu____13200  in
                        let uu____13236 =
                          let uu____13239 =
                            let uu____13240 =
                              let uu____13247 =
                                let uu____13248 =
                                  let uu____13259 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp)
                                     in
                                  ([[xtok_app]], vars, uu____13259)  in
                                FStar_SMTEncoding_Util.mkForall uu____13248
                                 in
                              (uu____13247,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1))
                               in
                            FStar_SMTEncoding_Util.mkAssume uu____13240  in
                          [uu____13239]  in
                        uu____13199 :: uu____13236  in
                      xtok_decl :: uu____13196  in
                    xname_decl :: uu____13193  in
                  (xtok1, uu____13190)  in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)]  in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)]  in
                let prims1 =
                  let uu____13350 =
                    let uu____13363 =
                      let uu____13372 =
                        let uu____13373 = FStar_SMTEncoding_Util.mkEq (x, y)
                           in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____13373
                         in
                      quant axy uu____13372  in
                    (FStar_Parser_Const.op_Eq, uu____13363)  in
                  let uu____13382 =
                    let uu____13397 =
                      let uu____13410 =
                        let uu____13419 =
                          let uu____13420 =
                            let uu____13421 =
                              FStar_SMTEncoding_Util.mkEq (x, y)  in
                            FStar_SMTEncoding_Util.mkNot uu____13421  in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____13420
                           in
                        quant axy uu____13419  in
                      (FStar_Parser_Const.op_notEq, uu____13410)  in
                    let uu____13430 =
                      let uu____13445 =
                        let uu____13458 =
                          let uu____13467 =
                            let uu____13468 =
                              let uu____13469 =
                                let uu____13474 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____13475 =
                                  FStar_SMTEncoding_Term.unboxInt y  in
                                (uu____13474, uu____13475)  in
                              FStar_SMTEncoding_Util.mkLT uu____13469  in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____13468
                             in
                          quant xy uu____13467  in
                        (FStar_Parser_Const.op_LT, uu____13458)  in
                      let uu____13484 =
                        let uu____13499 =
                          let uu____13512 =
                            let uu____13521 =
                              let uu____13522 =
                                let uu____13523 =
                                  let uu____13528 =
                                    FStar_SMTEncoding_Term.unboxInt x  in
                                  let uu____13529 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  (uu____13528, uu____13529)  in
                                FStar_SMTEncoding_Util.mkLTE uu____13523  in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____13522
                               in
                            quant xy uu____13521  in
                          (FStar_Parser_Const.op_LTE, uu____13512)  in
                        let uu____13538 =
                          let uu____13553 =
                            let uu____13566 =
                              let uu____13575 =
                                let uu____13576 =
                                  let uu____13577 =
                                    let uu____13582 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    let uu____13583 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    (uu____13582, uu____13583)  in
                                  FStar_SMTEncoding_Util.mkGT uu____13577  in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____13576
                                 in
                              quant xy uu____13575  in
                            (FStar_Parser_Const.op_GT, uu____13566)  in
                          let uu____13592 =
                            let uu____13607 =
                              let uu____13620 =
                                let uu____13629 =
                                  let uu____13630 =
                                    let uu____13631 =
                                      let uu____13636 =
                                        FStar_SMTEncoding_Term.unboxInt x  in
                                      let uu____13637 =
                                        FStar_SMTEncoding_Term.unboxInt y  in
                                      (uu____13636, uu____13637)  in
                                    FStar_SMTEncoding_Util.mkGTE uu____13631
                                     in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool
                                    uu____13630
                                   in
                                quant xy uu____13629  in
                              (FStar_Parser_Const.op_GTE, uu____13620)  in
                            let uu____13646 =
                              let uu____13661 =
                                let uu____13674 =
                                  let uu____13683 =
                                    let uu____13684 =
                                      let uu____13685 =
                                        let uu____13690 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        let uu____13691 =
                                          FStar_SMTEncoding_Term.unboxInt y
                                           in
                                        (uu____13690, uu____13691)  in
                                      FStar_SMTEncoding_Util.mkSub
                                        uu____13685
                                       in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____13684
                                     in
                                  quant xy uu____13683  in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____13674)
                                 in
                              let uu____13700 =
                                let uu____13715 =
                                  let uu____13728 =
                                    let uu____13737 =
                                      let uu____13738 =
                                        let uu____13739 =
                                          FStar_SMTEncoding_Term.unboxInt x
                                           in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____13739
                                         in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____13738
                                       in
                                    quant qx uu____13737  in
                                  (FStar_Parser_Const.op_Minus, uu____13728)
                                   in
                                let uu____13748 =
                                  let uu____13763 =
                                    let uu____13776 =
                                      let uu____13785 =
                                        let uu____13786 =
                                          let uu____13787 =
                                            let uu____13792 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x
                                               in
                                            let uu____13793 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y
                                               in
                                            (uu____13792, uu____13793)  in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____13787
                                           in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____13786
                                         in
                                      quant xy uu____13785  in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____13776)
                                     in
                                  let uu____13802 =
                                    let uu____13817 =
                                      let uu____13830 =
                                        let uu____13839 =
                                          let uu____13840 =
                                            let uu____13841 =
                                              let uu____13846 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x
                                                 in
                                              let uu____13847 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y
                                                 in
                                              (uu____13846, uu____13847)  in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____13841
                                             in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____13840
                                           in
                                        quant xy uu____13839  in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____13830)
                                       in
                                    let uu____13856 =
                                      let uu____13871 =
                                        let uu____13884 =
                                          let uu____13893 =
                                            let uu____13894 =
                                              let uu____13895 =
                                                let uu____13900 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x
                                                   in
                                                let uu____13901 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y
                                                   in
                                                (uu____13900, uu____13901)
                                                 in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____13895
                                               in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____13894
                                             in
                                          quant xy uu____13893  in
                                        (FStar_Parser_Const.op_Division,
                                          uu____13884)
                                         in
                                      let uu____13910 =
                                        let uu____13925 =
                                          let uu____13938 =
                                            let uu____13947 =
                                              let uu____13948 =
                                                let uu____13949 =
                                                  let uu____13954 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x
                                                     in
                                                  let uu____13955 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y
                                                     in
                                                  (uu____13954, uu____13955)
                                                   in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____13949
                                                 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____13948
                                               in
                                            quant xy uu____13947  in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____13938)
                                           in
                                        let uu____13964 =
                                          let uu____13979 =
                                            let uu____13992 =
                                              let uu____14001 =
                                                let uu____14002 =
                                                  let uu____14003 =
                                                    let uu____14008 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x
                                                       in
                                                    let uu____14009 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y
                                                       in
                                                    (uu____14008,
                                                      uu____14009)
                                                     in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____14003
                                                   in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____14002
                                                 in
                                              quant xy uu____14001  in
                                            (FStar_Parser_Const.op_And,
                                              uu____13992)
                                             in
                                          let uu____14018 =
                                            let uu____14033 =
                                              let uu____14046 =
                                                let uu____14055 =
                                                  let uu____14056 =
                                                    let uu____14057 =
                                                      let uu____14062 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      let uu____14063 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y
                                                         in
                                                      (uu____14062,
                                                        uu____14063)
                                                       in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____14057
                                                     in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____14056
                                                   in
                                                quant xy uu____14055  in
                                              (FStar_Parser_Const.op_Or,
                                                uu____14046)
                                               in
                                            let uu____14072 =
                                              let uu____14087 =
                                                let uu____14100 =
                                                  let uu____14109 =
                                                    let uu____14110 =
                                                      let uu____14111 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x
                                                         in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____14111
                                                       in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____14110
                                                     in
                                                  quant qx uu____14109  in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____14100)
                                                 in
                                              [uu____14087]  in
                                            uu____14033 :: uu____14072  in
                                          uu____13979 :: uu____14018  in
                                        uu____13925 :: uu____13964  in
                                      uu____13871 :: uu____13910  in
                                    uu____13817 :: uu____13856  in
                                  uu____13763 :: uu____13802  in
                                uu____13715 :: uu____13748  in
                              uu____13661 :: uu____13700  in
                            uu____13607 :: uu____13646  in
                          uu____13553 :: uu____13592  in
                        uu____13499 :: uu____13538  in
                      uu____13445 :: uu____13484  in
                    uu____13397 :: uu____13430  in
                  uu____13350 :: uu____13382  in
                let mk1 l v1 =
                  let uu____14325 =
                    let uu____14334 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____14392  ->
                              match uu____14392 with
                              | (l',uu____14406) ->
                                  FStar_Ident.lid_equals l l'))
                       in
                    FStar_All.pipe_right uu____14334
                      (FStar_Option.map
                         (fun uu____14466  ->
                            match uu____14466 with | (uu____14485,b) -> b v1))
                     in
                  FStar_All.pipe_right uu____14325 FStar_Option.get  in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____14556  ->
                          match uu____14556 with
                          | (l',uu____14570) -> FStar_Ident.lid_equals l l'))
                   in
                { mk = mk1; is }))
  
let (pretype_axiom :
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____14608 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
        match uu____14608 with
        | (xxsym,xx) ->
            let uu____14615 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort
               in
            (match uu____14615 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp  in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp  in
                 let module_name = env.current_module_name  in
                 let uu____14625 =
                   let uu____14632 =
                     let uu____14633 =
                       let uu____14644 =
                         let uu____14645 =
                           let uu____14650 =
                             let uu____14651 =
                               let uu____14656 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx])
                                  in
                               (tapp, uu____14656)  in
                             FStar_SMTEncoding_Util.mkEq uu____14651  in
                           (xx_has_type, uu____14650)  in
                         FStar_SMTEncoding_Util.mkImp uu____14645  in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____14644)
                        in
                     FStar_SMTEncoding_Util.mkForall uu____14633  in
                   let uu____14681 =
                     let uu____14682 =
                       let uu____14683 =
                         let uu____14684 =
                           FStar_Util.digest_of_string tapp_hash  in
                         Prims.strcat "_pretyping_" uu____14684  in
                       Prims.strcat module_name uu____14683  in
                     varops.mk_unique uu____14682  in
                   (uu____14632, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____14681)
                    in
                 FStar_SMTEncoding_Util.mkAssume uu____14625)
  
let (primitive_type_axioms :
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
  let x = FStar_SMTEncoding_Util.mkFreeV xx  in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort)  in
  let y = FStar_SMTEncoding_Util.mkFreeV yy  in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let uu____14720 =
      let uu____14721 =
        let uu____14728 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt
           in
        (uu____14728, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14721  in
    let uu____14731 =
      let uu____14734 =
        let uu____14735 =
          let uu____14742 =
            let uu____14743 =
              let uu____14754 =
                let uu____14755 =
                  let uu____14760 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit)
                     in
                  (typing_pred, uu____14760)  in
                FStar_SMTEncoding_Util.mkImp uu____14755  in
              ([[typing_pred]], [xx], uu____14754)  in
            mkForall_fuel uu____14743  in
          (uu____14742, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14735  in
      [uu____14734]  in
    uu____14720 :: uu____14731  in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____14802 =
      let uu____14803 =
        let uu____14810 =
          let uu____14811 =
            let uu____14822 =
              let uu____14827 =
                let uu____14830 = FStar_SMTEncoding_Term.boxBool b  in
                [uu____14830]  in
              [uu____14827]  in
            let uu____14835 =
              let uu____14836 = FStar_SMTEncoding_Term.boxBool b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14836 tt  in
            (uu____14822, [bb], uu____14835)  in
          FStar_SMTEncoding_Util.mkForall uu____14811  in
        (uu____14810, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14803  in
    let uu____14857 =
      let uu____14860 =
        let uu____14861 =
          let uu____14868 =
            let uu____14869 =
              let uu____14880 =
                let uu____14881 =
                  let uu____14886 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxBoolFun) x
                     in
                  (typing_pred, uu____14886)  in
                FStar_SMTEncoding_Util.mkImp uu____14881  in
              ([[typing_pred]], [xx], uu____14880)  in
            mkForall_fuel uu____14869  in
          (uu____14868, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____14861  in
      [uu____14860]  in
    uu____14802 :: uu____14857  in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt  in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let precedes =
      let uu____14936 =
        let uu____14937 =
          let uu____14944 =
            let uu____14947 =
              let uu____14950 =
                let uu____14953 = FStar_SMTEncoding_Term.boxInt a  in
                let uu____14954 =
                  let uu____14957 = FStar_SMTEncoding_Term.boxInt b  in
                  [uu____14957]  in
                uu____14953 :: uu____14954  in
              tt :: uu____14950  in
            tt :: uu____14947  in
          ("Prims.Precedes", uu____14944)  in
        FStar_SMTEncoding_Util.mkApp uu____14937  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14936  in
    let precedes_y_x =
      let uu____14961 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x])  in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____14961  in
    let uu____14964 =
      let uu____14965 =
        let uu____14972 =
          let uu____14973 =
            let uu____14984 =
              let uu____14989 =
                let uu____14992 = FStar_SMTEncoding_Term.boxInt b  in
                [uu____14992]  in
              [uu____14989]  in
            let uu____14997 =
              let uu____14998 = FStar_SMTEncoding_Term.boxInt b  in
              FStar_SMTEncoding_Term.mk_HasType uu____14998 tt  in
            (uu____14984, [bb], uu____14997)  in
          FStar_SMTEncoding_Util.mkForall uu____14973  in
        (uu____14972, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____14965  in
    let uu____15019 =
      let uu____15022 =
        let uu____15023 =
          let uu____15030 =
            let uu____15031 =
              let uu____15042 =
                let uu____15043 =
                  let uu____15048 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxIntFun) x
                     in
                  (typing_pred, uu____15048)  in
                FStar_SMTEncoding_Util.mkImp uu____15043  in
              ([[typing_pred]], [xx], uu____15042)  in
            mkForall_fuel uu____15031  in
          (uu____15030, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15023  in
      let uu____15073 =
        let uu____15076 =
          let uu____15077 =
            let uu____15084 =
              let uu____15085 =
                let uu____15096 =
                  let uu____15097 =
                    let uu____15102 =
                      let uu____15103 =
                        let uu____15106 =
                          let uu____15109 =
                            let uu____15112 =
                              let uu____15113 =
                                let uu____15118 =
                                  FStar_SMTEncoding_Term.unboxInt x  in
                                let uu____15119 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0")
                                   in
                                (uu____15118, uu____15119)  in
                              FStar_SMTEncoding_Util.mkGT uu____15113  in
                            let uu____15120 =
                              let uu____15123 =
                                let uu____15124 =
                                  let uu____15129 =
                                    FStar_SMTEncoding_Term.unboxInt y  in
                                  let uu____15130 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0")
                                     in
                                  (uu____15129, uu____15130)  in
                                FStar_SMTEncoding_Util.mkGTE uu____15124  in
                              let uu____15131 =
                                let uu____15134 =
                                  let uu____15135 =
                                    let uu____15140 =
                                      FStar_SMTEncoding_Term.unboxInt y  in
                                    let uu____15141 =
                                      FStar_SMTEncoding_Term.unboxInt x  in
                                    (uu____15140, uu____15141)  in
                                  FStar_SMTEncoding_Util.mkLT uu____15135  in
                                [uu____15134]  in
                              uu____15123 :: uu____15131  in
                            uu____15112 :: uu____15120  in
                          typing_pred_y :: uu____15109  in
                        typing_pred :: uu____15106  in
                      FStar_SMTEncoding_Util.mk_and_l uu____15103  in
                    (uu____15102, precedes_y_x)  in
                  FStar_SMTEncoding_Util.mkImp uu____15097  in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____15096)
                 in
              mkForall_fuel uu____15085  in
            (uu____15084,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat")
             in
          FStar_SMTEncoding_Util.mkAssume uu____15077  in
        [uu____15076]  in
      uu____15022 :: uu____15073  in
    uu____14964 :: uu____15019  in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt  in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort)  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let uu____15187 =
      let uu____15188 =
        let uu____15195 =
          let uu____15196 =
            let uu____15207 =
              let uu____15212 =
                let uu____15215 = FStar_SMTEncoding_Term.boxString b  in
                [uu____15215]  in
              [uu____15212]  in
            let uu____15220 =
              let uu____15221 = FStar_SMTEncoding_Term.boxString b  in
              FStar_SMTEncoding_Term.mk_HasType uu____15221 tt  in
            (uu____15207, [bb], uu____15220)  in
          FStar_SMTEncoding_Util.mkForall uu____15196  in
        (uu____15195, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15188  in
    let uu____15242 =
      let uu____15245 =
        let uu____15246 =
          let uu____15253 =
            let uu____15254 =
              let uu____15265 =
                let uu____15266 =
                  let uu____15271 =
                    FStar_SMTEncoding_Term.mk_tester
                      (FStar_Pervasives_Native.fst
                         FStar_SMTEncoding_Term.boxStringFun) x
                     in
                  (typing_pred, uu____15271)  in
                FStar_SMTEncoding_Util.mkImp uu____15266  in
              ([[typing_pred]], [xx], uu____15265)  in
            mkForall_fuel uu____15254  in
          (uu____15253, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion")
           in
        FStar_SMTEncoding_Util.mkAssume uu____15246  in
      [uu____15245]  in
    uu____15187 :: uu____15242  in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm])  in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")]
     in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm])  in
    let uu____15324 =
      let uu____15325 =
        let uu____15332 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid)
           in
        (uu____15332, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15325  in
    [uu____15324]  in
  let mk_and_interp env conj uu____15344 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15369 =
      let uu____15370 =
        let uu____15377 =
          let uu____15378 =
            let uu____15389 =
              let uu____15390 =
                let uu____15395 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b)  in
                (uu____15395, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15390  in
            ([[l_and_a_b]], [aa; bb], uu____15389)  in
          FStar_SMTEncoding_Util.mkForall uu____15378  in
        (uu____15377, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15370  in
    [uu____15369]  in
  let mk_or_interp env disj uu____15433 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15458 =
      let uu____15459 =
        let uu____15466 =
          let uu____15467 =
            let uu____15478 =
              let uu____15479 =
                let uu____15484 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b)  in
                (uu____15484, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15479  in
            ([[l_or_a_b]], [aa; bb], uu____15478)  in
          FStar_SMTEncoding_Util.mkForall uu____15467  in
        (uu____15466, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15459  in
    [uu____15458]  in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort)  in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1  in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1  in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y])  in
    let uu____15547 =
      let uu____15548 =
        let uu____15555 =
          let uu____15556 =
            let uu____15567 =
              let uu____15568 =
                let uu____15573 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15573, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15568  in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____15567)  in
          FStar_SMTEncoding_Util.mkForall uu____15556  in
        (uu____15555, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15548  in
    [uu____15547]  in
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
    let uu____15646 =
      let uu____15647 =
        let uu____15654 =
          let uu____15655 =
            let uu____15666 =
              let uu____15667 =
                let uu____15672 = FStar_SMTEncoding_Util.mkEq (x1, y1)  in
                (uu____15672, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15667  in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____15666)  in
          FStar_SMTEncoding_Util.mkForall uu____15655  in
        (uu____15654, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15647  in
    [uu____15646]  in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15743 =
      let uu____15744 =
        let uu____15751 =
          let uu____15752 =
            let uu____15763 =
              let uu____15764 =
                let uu____15769 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b)  in
                (uu____15769, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15764  in
            ([[l_imp_a_b]], [aa; bb], uu____15763)  in
          FStar_SMTEncoding_Util.mkForall uu____15752  in
        (uu____15751, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15744  in
    [uu____15743]  in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let b = FStar_SMTEncoding_Util.mkFreeV bb  in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b])  in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b])  in
    let uu____15832 =
      let uu____15833 =
        let uu____15840 =
          let uu____15841 =
            let uu____15852 =
              let uu____15853 =
                let uu____15858 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b)  in
                (uu____15858, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____15853  in
            ([[l_iff_a_b]], [aa; bb], uu____15852)  in
          FStar_SMTEncoding_Util.mkForall uu____15841  in
        (uu____15840, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15833  in
    [uu____15832]  in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort)  in
    let a = FStar_SMTEncoding_Util.mkFreeV aa  in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a])  in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a])  in
    let not_valid_a =
      let uu____15910 = FStar_SMTEncoding_Util.mkApp ("Valid", [a])  in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____15910  in
    let uu____15913 =
      let uu____15914 =
        let uu____15921 =
          let uu____15922 =
            let uu____15933 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid)  in
            ([[l_not_a]], [aa], uu____15933)  in
          FStar_SMTEncoding_Util.mkForall uu____15922  in
        (uu____15921, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____15914  in
    [uu____15913]  in
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
      let uu____15993 =
        let uu____16000 =
          let uu____16003 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16003]  in
        ("Valid", uu____16000)  in
      FStar_SMTEncoding_Util.mkApp uu____15993  in
    let uu____16006 =
      let uu____16007 =
        let uu____16014 =
          let uu____16015 =
            let uu____16026 =
              let uu____16027 =
                let uu____16032 =
                  let uu____16033 =
                    let uu____16044 =
                      let uu____16049 =
                        let uu____16052 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16052]  in
                      [uu____16049]  in
                    let uu____16057 =
                      let uu____16058 =
                        let uu____16063 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16063, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16058  in
                    (uu____16044, [xx1], uu____16057)  in
                  FStar_SMTEncoding_Util.mkForall uu____16033  in
                (uu____16032, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16027  in
            ([[l_forall_a_b]], [aa; bb], uu____16026)  in
          FStar_SMTEncoding_Util.mkForall uu____16015  in
        (uu____16014, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16007  in
    [uu____16006]  in
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
      let uu____16145 =
        let uu____16152 =
          let uu____16155 = FStar_SMTEncoding_Util.mk_ApplyTT b x1  in
          [uu____16155]  in
        ("Valid", uu____16152)  in
      FStar_SMTEncoding_Util.mkApp uu____16145  in
    let uu____16158 =
      let uu____16159 =
        let uu____16166 =
          let uu____16167 =
            let uu____16178 =
              let uu____16179 =
                let uu____16184 =
                  let uu____16185 =
                    let uu____16196 =
                      let uu____16201 =
                        let uu____16204 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        [uu____16204]  in
                      [uu____16201]  in
                    let uu____16209 =
                      let uu____16210 =
                        let uu____16215 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a  in
                        (uu____16215, valid_b_x)  in
                      FStar_SMTEncoding_Util.mkImp uu____16210  in
                    (uu____16196, [xx1], uu____16209)  in
                  FStar_SMTEncoding_Util.mkExists uu____16185  in
                (uu____16184, valid)  in
              FStar_SMTEncoding_Util.mkIff uu____16179  in
            ([[l_exists_a_b]], [aa; bb], uu____16178)  in
          FStar_SMTEncoding_Util.mkForall uu____16167  in
        (uu____16166, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16159  in
    [uu____16158]  in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, [])  in
    let uu____16275 =
      let uu____16276 =
        let uu____16283 =
          let uu____16284 = FStar_SMTEncoding_Term.mk_Range_const ()  in
          FStar_SMTEncoding_Term.mk_HasTypeZ uu____16284 range_ty  in
        let uu____16285 = varops.mk_unique "typing_range_const"  in
        (uu____16283, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____16285)
         in
      FStar_SMTEncoding_Util.mkAssume uu____16276  in
    [uu____16275]  in
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
        let uu____16319 = FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1")
           in
        FStar_SMTEncoding_Term.mk_HasTypeFuel uu____16319 x1 t  in
      let uu____16320 =
        let uu____16331 = FStar_SMTEncoding_Util.mkImp (hastypeZ, hastypeS)
           in
        ([[hastypeZ]], [xx1], uu____16331)  in
      FStar_SMTEncoding_Util.mkForall uu____16320  in
    let uu____16354 =
      let uu____16355 =
        let uu____16362 =
          let uu____16363 =
            let uu____16374 = FStar_SMTEncoding_Util.mkImp (valid, body)  in
            ([[inversion_t]], [tt1], uu____16374)  in
          FStar_SMTEncoding_Util.mkForall uu____16363  in
        (uu____16362,
          (FStar_Pervasives_Native.Some "inversion interpretation"),
          "inversion-interp")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16355  in
    [uu____16354]  in
  let mk_with_type_axiom env with_type1 tt =
    let tt1 = ("t", FStar_SMTEncoding_Term.Term_sort)  in
    let t = FStar_SMTEncoding_Util.mkFreeV tt1  in
    let ee = ("e", FStar_SMTEncoding_Term.Term_sort)  in
    let e = FStar_SMTEncoding_Util.mkFreeV ee  in
    let with_type_t_e = FStar_SMTEncoding_Util.mkApp (with_type1, [t; e])  in
    let uu____16424 =
      let uu____16425 =
        let uu____16432 =
          let uu____16433 =
            let uu____16448 =
              let uu____16449 =
                let uu____16454 =
                  FStar_SMTEncoding_Util.mkEq (with_type_t_e, e)  in
                let uu____16455 =
                  FStar_SMTEncoding_Term.mk_HasType with_type_t_e t  in
                (uu____16454, uu____16455)  in
              FStar_SMTEncoding_Util.mkAnd uu____16449  in
            ([[with_type_t_e]],
              (FStar_Pervasives_Native.Some (Prims.parse_int "0")),
              [tt1; ee], uu____16448)
             in
          FStar_SMTEncoding_Util.mkForall' uu____16433  in
        (uu____16432,
          (FStar_Pervasives_Native.Some "with_type primitive axiom"),
          "@with_type_primitive_axiom")
         in
      FStar_SMTEncoding_Util.mkAssume uu____16425  in
    [uu____16424]  in
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
    (FStar_Parser_Const.inversion_lid, mk_inversion_axiom);
    (FStar_Parser_Const.with_type_lid, mk_with_type_axiom)]  in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____16801 =
            FStar_Util.find_opt
              (fun uu____16827  ->
                 match uu____16827 with
                 | (l,uu____16839) -> FStar_Ident.lid_equals l t) prims1
             in
          match uu____16801 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____16864,f) -> f env s tt
  
let (encode_smt_lemma :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list)
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
        let uu____16900 = encode_function_type_as_formula t env  in
        match uu____16900 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
  
let (encode_free_var :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.term ->
            FStar_Syntax_Syntax.qualifier Prims.list ->
              (FStar_SMTEncoding_Term.decl Prims.list,env_t)
                FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun fv  ->
        fun tt  ->
          fun t_norm  ->
            fun quals  ->
              let lid =
                (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
              let uu____16940 =
                ((let uu____16943 =
                    (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                      (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                         t_norm)
                     in
                  FStar_All.pipe_left Prims.op_Negation uu____16943) ||
                   (FStar_Syntax_Util.is_lemma t_norm))
                  || uninterpreted
                 in
              if uu____16940
              then
                let uu____16950 = new_term_constant_and_tok_from_lid env lid
                   in
                match uu____16950 with
                | (vname,vtok,env1) ->
                    let arg_sorts =
                      let uu____16969 =
                        let uu____16970 = FStar_Syntax_Subst.compress t_norm
                           in
                        uu____16970.FStar_Syntax_Syntax.n  in
                      match uu____16969 with
                      | FStar_Syntax_Syntax.Tm_arrow (binders,uu____16976) ->
                          FStar_All.pipe_right binders
                            (FStar_List.map
                               (fun uu____17006  ->
                                  FStar_SMTEncoding_Term.Term_sort))
                      | uu____17011 -> []  in
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
                (let uu____17025 = prims.is lid  in
                 if uu____17025
                 then
                   let vname = varops.new_fvar lid  in
                   let uu____17033 = prims.mk lid vname  in
                   match uu____17033 with
                   | (tok,definition) ->
                       let env1 =
                         push_free_var env lid vname
                           (FStar_Pervasives_Native.Some tok)
                          in
                       (definition, env1)
                 else
                   (let encode_non_total_function_typ =
                      lid.FStar_Ident.nsstr <> "Prims"  in
                    let uu____17057 =
                      let uu____17068 = curried_arrow_formals_comp t_norm  in
                      match uu____17068 with
                      | (args,comp) ->
                          let comp1 =
                            let uu____17086 =
                              FStar_TypeChecker_Env.is_reifiable_comp
                                env.tcenv comp
                               in
                            if uu____17086
                            then
                              let uu____17087 =
                                FStar_TypeChecker_Env.reify_comp
                                  (let uu___117_17090 = env.tcenv  in
                                   {
                                     FStar_TypeChecker_Env.solver =
                                       (uu___117_17090.FStar_TypeChecker_Env.solver);
                                     FStar_TypeChecker_Env.range =
                                       (uu___117_17090.FStar_TypeChecker_Env.range);
                                     FStar_TypeChecker_Env.curmodule =
                                       (uu___117_17090.FStar_TypeChecker_Env.curmodule);
                                     FStar_TypeChecker_Env.gamma =
                                       (uu___117_17090.FStar_TypeChecker_Env.gamma);
                                     FStar_TypeChecker_Env.gamma_cache =
                                       (uu___117_17090.FStar_TypeChecker_Env.gamma_cache);
                                     FStar_TypeChecker_Env.modules =
                                       (uu___117_17090.FStar_TypeChecker_Env.modules);
                                     FStar_TypeChecker_Env.expected_typ =
                                       (uu___117_17090.FStar_TypeChecker_Env.expected_typ);
                                     FStar_TypeChecker_Env.sigtab =
                                       (uu___117_17090.FStar_TypeChecker_Env.sigtab);
                                     FStar_TypeChecker_Env.is_pattern =
                                       (uu___117_17090.FStar_TypeChecker_Env.is_pattern);
                                     FStar_TypeChecker_Env.instantiate_imp =
                                       (uu___117_17090.FStar_TypeChecker_Env.instantiate_imp);
                                     FStar_TypeChecker_Env.effects =
                                       (uu___117_17090.FStar_TypeChecker_Env.effects);
                                     FStar_TypeChecker_Env.generalize =
                                       (uu___117_17090.FStar_TypeChecker_Env.generalize);
                                     FStar_TypeChecker_Env.letrecs =
                                       (uu___117_17090.FStar_TypeChecker_Env.letrecs);
                                     FStar_TypeChecker_Env.top_level =
                                       (uu___117_17090.FStar_TypeChecker_Env.top_level);
                                     FStar_TypeChecker_Env.check_uvars =
                                       (uu___117_17090.FStar_TypeChecker_Env.check_uvars);
                                     FStar_TypeChecker_Env.use_eq =
                                       (uu___117_17090.FStar_TypeChecker_Env.use_eq);
                                     FStar_TypeChecker_Env.is_iface =
                                       (uu___117_17090.FStar_TypeChecker_Env.is_iface);
                                     FStar_TypeChecker_Env.admit =
                                       (uu___117_17090.FStar_TypeChecker_Env.admit);
                                     FStar_TypeChecker_Env.lax = true;
                                     FStar_TypeChecker_Env.lax_universes =
                                       (uu___117_17090.FStar_TypeChecker_Env.lax_universes);
                                     FStar_TypeChecker_Env.failhard =
                                       (uu___117_17090.FStar_TypeChecker_Env.failhard);
                                     FStar_TypeChecker_Env.nosynth =
                                       (uu___117_17090.FStar_TypeChecker_Env.nosynth);
                                     FStar_TypeChecker_Env.tc_term =
                                       (uu___117_17090.FStar_TypeChecker_Env.tc_term);
                                     FStar_TypeChecker_Env.type_of =
                                       (uu___117_17090.FStar_TypeChecker_Env.type_of);
                                     FStar_TypeChecker_Env.universe_of =
                                       (uu___117_17090.FStar_TypeChecker_Env.universe_of);
                                     FStar_TypeChecker_Env.use_bv_sorts =
                                       (uu___117_17090.FStar_TypeChecker_Env.use_bv_sorts);
                                     FStar_TypeChecker_Env.qname_and_index =
                                       (uu___117_17090.FStar_TypeChecker_Env.qname_and_index);
                                     FStar_TypeChecker_Env.proof_ns =
                                       (uu___117_17090.FStar_TypeChecker_Env.proof_ns);
                                     FStar_TypeChecker_Env.synth =
                                       (uu___117_17090.FStar_TypeChecker_Env.synth);
                                     FStar_TypeChecker_Env.is_native_tactic =
                                       (uu___117_17090.FStar_TypeChecker_Env.is_native_tactic);
                                     FStar_TypeChecker_Env.identifier_info =
                                       (uu___117_17090.FStar_TypeChecker_Env.identifier_info);
                                     FStar_TypeChecker_Env.tc_hooks =
                                       (uu___117_17090.FStar_TypeChecker_Env.tc_hooks);
                                     FStar_TypeChecker_Env.dsenv =
                                       (uu___117_17090.FStar_TypeChecker_Env.dsenv);
                                     FStar_TypeChecker_Env.dep_graph =
                                       (uu___117_17090.FStar_TypeChecker_Env.dep_graph)
                                   }) comp FStar_Syntax_Syntax.U_unknown
                                 in
                              FStar_Syntax_Syntax.mk_Total uu____17087
                            else comp  in
                          if encode_non_total_function_typ
                          then
                            let uu____17102 =
                              FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                                env.tcenv comp1
                               in
                            (args, uu____17102)
                          else
                            (args,
                              (FStar_Pervasives_Native.None,
                                (FStar_Syntax_Util.comp_result comp1)))
                       in
                    match uu____17057 with
                    | (formals,(pre_opt,res_t)) ->
                        let uu____17147 =
                          new_term_constant_and_tok_from_lid env lid  in
                        (match uu____17147 with
                         | (vname,vtok,env1) ->
                             let vtok_tm =
                               match formals with
                               | [] ->
                                   FStar_SMTEncoding_Util.mkFreeV
                                     (vname,
                                       FStar_SMTEncoding_Term.Term_sort)
                               | uu____17168 ->
                                   FStar_SMTEncoding_Util.mkApp (vtok, [])
                                in
                             let mk_disc_proj_axioms guard encoded_res_t vapp
                               vars =
                               FStar_All.pipe_right quals
                                 (FStar_List.collect
                                    (fun uu___89_17210  ->
                                       match uu___89_17210 with
                                       | FStar_Syntax_Syntax.Discriminator d
                                           ->
                                           let uu____17214 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17214 with
                                            | (uu____17235,(xxsym,uu____17237))
                                                ->
                                                let xx =
                                                  FStar_SMTEncoding_Util.mkFreeV
                                                    (xxsym,
                                                      FStar_SMTEncoding_Term.Term_sort)
                                                   in
                                                let uu____17255 =
                                                  let uu____17256 =
                                                    let uu____17263 =
                                                      let uu____17264 =
                                                        let uu____17275 =
                                                          let uu____17276 =
                                                            let uu____17281 =
                                                              let uu____17282
                                                                =
                                                                FStar_SMTEncoding_Term.mk_tester
                                                                  (escape
                                                                    d.FStar_Ident.str)
                                                                  xx
                                                                 in
                                                              FStar_All.pipe_left
                                                                FStar_SMTEncoding_Term.boxBool
                                                                uu____17282
                                                               in
                                                            (vapp,
                                                              uu____17281)
                                                             in
                                                          FStar_SMTEncoding_Util.mkEq
                                                            uu____17276
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17275)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17264
                                                       in
                                                    (uu____17263,
                                                      (FStar_Pervasives_Native.Some
                                                         "Discriminator equation"),
                                                      (Prims.strcat
                                                         "disc_equation_"
                                                         (escape
                                                            d.FStar_Ident.str)))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17256
                                                   in
                                                [uu____17255])
                                       | FStar_Syntax_Syntax.Projector 
                                           (d,f) ->
                                           let uu____17301 =
                                             FStar_Util.prefix vars  in
                                           (match uu____17301 with
                                            | (uu____17322,(xxsym,uu____17324))
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
                                                let uu____17347 =
                                                  let uu____17348 =
                                                    let uu____17355 =
                                                      let uu____17356 =
                                                        let uu____17367 =
                                                          FStar_SMTEncoding_Util.mkEq
                                                            (vapp, prim_app)
                                                           in
                                                        ([[vapp]], vars,
                                                          uu____17367)
                                                         in
                                                      FStar_SMTEncoding_Util.mkForall
                                                        uu____17356
                                                       in
                                                    (uu____17355,
                                                      (FStar_Pervasives_Native.Some
                                                         "Projector equation"),
                                                      (Prims.strcat
                                                         "proj_equation_"
                                                         tp_name))
                                                     in
                                                  FStar_SMTEncoding_Util.mkAssume
                                                    uu____17348
                                                   in
                                                [uu____17347])
                                       | uu____17384 -> []))
                                in
                             let uu____17385 =
                               encode_binders FStar_Pervasives_Native.None
                                 formals env1
                                in
                             (match uu____17385 with
                              | (vars,guards,env',decls1,uu____17412) ->
                                  let uu____17425 =
                                    match pre_opt with
                                    | FStar_Pervasives_Native.None  ->
                                        let uu____17434 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            guards
                                           in
                                        (uu____17434, decls1)
                                    | FStar_Pervasives_Native.Some p ->
                                        let uu____17436 =
                                          encode_formula p env'  in
                                        (match uu____17436 with
                                         | (g,ds) ->
                                             let uu____17447 =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 (g :: guards)
                                                in
                                             (uu____17447,
                                               (FStar_List.append decls1 ds)))
                                     in
                                  (match uu____17425 with
                                   | (guard,decls11) ->
                                       let vtok_app = mk_Apply vtok_tm vars
                                          in
                                       let vapp =
                                         let uu____17460 =
                                           let uu____17467 =
                                             FStar_List.map
                                               FStar_SMTEncoding_Util.mkFreeV
                                               vars
                                              in
                                           (vname, uu____17467)  in
                                         FStar_SMTEncoding_Util.mkApp
                                           uu____17460
                                          in
                                       let uu____17476 =
                                         let vname_decl =
                                           let uu____17484 =
                                             let uu____17495 =
                                               FStar_All.pipe_right formals
                                                 (FStar_List.map
                                                    (fun uu____17505  ->
                                                       FStar_SMTEncoding_Term.Term_sort))
                                                in
                                             (vname, uu____17495,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None)
                                              in
                                           FStar_SMTEncoding_Term.DeclFun
                                             uu____17484
                                            in
                                         let uu____17514 =
                                           let env2 =
                                             let uu___118_17520 = env1  in
                                             {
                                               bindings =
                                                 (uu___118_17520.bindings);
                                               depth = (uu___118_17520.depth);
                                               tcenv = (uu___118_17520.tcenv);
                                               warn = (uu___118_17520.warn);
                                               cache = (uu___118_17520.cache);
                                               nolabels =
                                                 (uu___118_17520.nolabels);
                                               use_zfuel_name =
                                                 (uu___118_17520.use_zfuel_name);
                                               encode_non_total_function_typ;
                                               current_module_name =
                                                 (uu___118_17520.current_module_name)
                                             }  in
                                           let uu____17521 =
                                             let uu____17522 =
                                               head_normal env2 tt  in
                                             Prims.op_Negation uu____17522
                                              in
                                           if uu____17521
                                           then
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               tt env2 vtok_tm
                                           else
                                             encode_term_pred
                                               FStar_Pervasives_Native.None
                                               t_norm env2 vtok_tm
                                            in
                                         match uu____17514 with
                                         | (tok_typing,decls2) ->
                                             let tok_typing1 =
                                               match formals with
                                               | uu____17537::uu____17538 ->
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
                                                     let uu____17578 =
                                                       let uu____17589 =
                                                         FStar_SMTEncoding_Term.mk_NoHoist
                                                           f tok_typing
                                                          in
                                                       ([[vtok_app_l];
                                                        [vtok_app_r]], 
                                                         [ff], uu____17589)
                                                        in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____17578
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (guarded_tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                               | uu____17616 ->
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     (tok_typing,
                                                       (FStar_Pervasives_Native.Some
                                                          "function token typing"),
                                                       (Prims.strcat
                                                          "function_token_typing_"
                                                          vname))
                                                in
                                             let uu____17619 =
                                               match formals with
                                               | [] ->
                                                   let uu____17636 =
                                                     let uu____17637 =
                                                       let uu____17640 =
                                                         FStar_SMTEncoding_Util.mkFreeV
                                                           (vname,
                                                             FStar_SMTEncoding_Term.Term_sort)
                                                          in
                                                       FStar_All.pipe_left
                                                         (fun _0_42  ->
                                                            FStar_Pervasives_Native.Some
                                                              _0_42)
                                                         uu____17640
                                                        in
                                                     push_free_var env1 lid
                                                       vname uu____17637
                                                      in
                                                   ((FStar_List.append decls2
                                                       [tok_typing1]),
                                                     uu____17636)
                                               | uu____17645 ->
                                                   let vtok_decl =
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       (vtok, [],
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         FStar_Pervasives_Native.None)
                                                      in
                                                   let name_tok_corr =
                                                     let uu____17652 =
                                                       let uu____17659 =
                                                         let uu____17660 =
                                                           let uu____17671 =
                                                             FStar_SMTEncoding_Util.mkEq
                                                               (vtok_app,
                                                                 vapp)
                                                              in
                                                           ([[vtok_app];
                                                            [vapp]], vars,
                                                             uu____17671)
                                                            in
                                                         FStar_SMTEncoding_Util.mkForall
                                                           uu____17660
                                                          in
                                                       (uu____17659,
                                                         (FStar_Pervasives_Native.Some
                                                            "Name-token correspondence"),
                                                         (Prims.strcat
                                                            "token_correspondence_"
                                                            vname))
                                                        in
                                                     FStar_SMTEncoding_Util.mkAssume
                                                       uu____17652
                                                      in
                                                   ((FStar_List.append decls2
                                                       [vtok_decl;
                                                       name_tok_corr;
                                                       tok_typing1]), env1)
                                                in
                                             (match uu____17619 with
                                              | (tok_decl,env2) ->
                                                  ((vname_decl :: tok_decl),
                                                    env2))
                                          in
                                       (match uu____17476 with
                                        | (decls2,env2) ->
                                            let uu____17714 =
                                              let res_t1 =
                                                FStar_Syntax_Subst.compress
                                                  res_t
                                                 in
                                              let uu____17722 =
                                                encode_term res_t1 env'  in
                                              match uu____17722 with
                                              | (encoded_res_t,decls) ->
                                                  let uu____17735 =
                                                    FStar_SMTEncoding_Term.mk_HasType
                                                      vapp encoded_res_t
                                                     in
                                                  (encoded_res_t,
                                                    uu____17735, decls)
                                               in
                                            (match uu____17714 with
                                             | (encoded_res_t,ty_pred,decls3)
                                                 ->
                                                 let typingAx =
                                                   let uu____17746 =
                                                     let uu____17753 =
                                                       let uu____17754 =
                                                         let uu____17765 =
                                                           FStar_SMTEncoding_Util.mkImp
                                                             (guard, ty_pred)
                                                            in
                                                         ([[vapp]], vars,
                                                           uu____17765)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____17754
                                                        in
                                                     (uu____17753,
                                                       (FStar_Pervasives_Native.Some
                                                          "free var typing"),
                                                       (Prims.strcat
                                                          "typing_" vname))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____17746
                                                    in
                                                 let freshness =
                                                   let uu____17781 =
                                                     FStar_All.pipe_right
                                                       quals
                                                       (FStar_List.contains
                                                          FStar_Syntax_Syntax.New)
                                                      in
                                                   if uu____17781
                                                   then
                                                     let uu____17786 =
                                                       let uu____17787 =
                                                         let uu____17798 =
                                                           FStar_All.pipe_right
                                                             vars
                                                             (FStar_List.map
                                                                FStar_Pervasives_Native.snd)
                                                            in
                                                         let uu____17809 =
                                                           varops.next_id ()
                                                            in
                                                         (vname, uu____17798,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           uu____17809)
                                                          in
                                                       FStar_SMTEncoding_Term.fresh_constructor
                                                         uu____17787
                                                        in
                                                     let uu____17812 =
                                                       let uu____17815 =
                                                         pretype_axiom env2
                                                           vapp vars
                                                          in
                                                       [uu____17815]  in
                                                     uu____17786 ::
                                                       uu____17812
                                                   else []  in
                                                 let g =
                                                   let uu____17820 =
                                                     let uu____17823 =
                                                       let uu____17826 =
                                                         let uu____17829 =
                                                           let uu____17832 =
                                                             mk_disc_proj_axioms
                                                               guard
                                                               encoded_res_t
                                                               vapp vars
                                                              in
                                                           typingAx ::
                                                             uu____17832
                                                            in
                                                         FStar_List.append
                                                           freshness
                                                           uu____17829
                                                          in
                                                       FStar_List.append
                                                         decls3 uu____17826
                                                        in
                                                     FStar_List.append decls2
                                                       uu____17823
                                                      in
                                                   FStar_List.append decls11
                                                     uu____17820
                                                    in
                                                 (g, env2))))))))
  
let (declare_top_level_let :
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string,FStar_SMTEncoding_Term.term
                           FStar_Pervasives_Native.option)
             FStar_Pervasives_Native.tuple2,FStar_SMTEncoding_Term.decl
                                              Prims.list,env_t)
            FStar_Pervasives_Native.tuple3)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____17863 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          match uu____17863 with
          | FStar_Pervasives_Native.None  ->
              let uu____17900 = encode_free_var false env x t t_norm []  in
              (match uu____17900 with
               | (decls,env1) ->
                   let uu____17927 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                      in
                   (match uu____17927 with
                    | (n1,x',uu____17954) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____17975) ->
              ((n1, x1), [], env)
  
let (encode_top_level_val :
  Prims.bool ->
    env_t ->
      FStar_Syntax_Syntax.fv ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2)
  =
  fun uninterpreted  ->
    fun env  ->
      fun lid  ->
        fun t  ->
          fun quals  ->
            let tt = norm env t  in
            let uu____18030 =
              encode_free_var uninterpreted env lid t tt quals  in
            match uu____18030 with
            | (decls,env1) ->
                let uu____18049 = FStar_Syntax_Util.is_smt_lemma t  in
                if uu____18049
                then
                  let uu____18056 =
                    let uu____18059 = encode_smt_lemma env1 lid tt  in
                    FStar_List.append decls uu____18059  in
                  (uu____18056, env1)
                else (decls, env1)
  
let (encode_top_level_vals :
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____18111  ->
                fun lb  ->
                  match uu____18111 with
                  | (decls,env1) ->
                      let uu____18131 =
                        let uu____18138 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                        encode_top_level_val false env1 uu____18138
                          lb.FStar_Syntax_Syntax.lbtyp quals
                         in
                      (match uu____18131 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
  
let (is_tactic : FStar_Syntax_Syntax.term -> Prims.bool) =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"]  in
    let uu____18159 = FStar_Syntax_Util.head_and_args t  in
    match uu____18159 with
    | (hd1,args) ->
        let uu____18196 =
          let uu____18197 = FStar_Syntax_Util.un_uinst hd1  in
          uu____18197.FStar_Syntax_Syntax.n  in
        (match uu____18196 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____18201,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c  in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____18220 -> false)
  
let (encode_top_level_let :
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun uu____18242  ->
      fun quals  ->
        match uu____18242 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders  in
              let uu____18318 = FStar_Util.first_N nbinders formals  in
              match uu____18318 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____18399  ->
                         fun uu____18400  ->
                           match (uu____18399, uu____18400) with
                           | ((formal,uu____18418),(binder,uu____18420)) ->
                               let uu____18429 =
                                 let uu____18436 =
                                   FStar_Syntax_Syntax.bv_to_name binder  in
                                 (formal, uu____18436)  in
                               FStar_Syntax_Syntax.NT uu____18429) formals1
                      binders
                     in
                  let extra_formals1 =
                    let uu____18444 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____18475  ->
                              match uu____18475 with
                              | (x,i) ->
                                  let uu____18486 =
                                    let uu___119_18487 = x  in
                                    let uu____18488 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort
                                       in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___119_18487.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___119_18487.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____18488
                                    }  in
                                  (uu____18486, i)))
                       in
                    FStar_All.pipe_right uu____18444
                      FStar_Syntax_Util.name_binders
                     in
                  let body1 =
                    let uu____18506 =
                      let uu____18507 = FStar_Syntax_Subst.compress body  in
                      let uu____18508 =
                        let uu____18509 =
                          FStar_Syntax_Util.args_of_binders extra_formals1
                           in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____18509
                         in
                      FStar_Syntax_Syntax.extend_app_n uu____18507
                        uu____18508
                       in
                    uu____18506 FStar_Pervasives_Native.None
                      body.FStar_Syntax_Syntax.pos
                     in
                  ((FStar_List.append binders extra_formals1), body1)
               in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____18570 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c  in
                if uu____18570
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___120_18573 = env.tcenv  in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___120_18573.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___120_18573.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___120_18573.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___120_18573.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___120_18573.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___120_18573.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___120_18573.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___120_18573.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___120_18573.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___120_18573.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___120_18573.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___120_18573.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___120_18573.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___120_18573.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___120_18573.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___120_18573.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___120_18573.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___120_18573.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___120_18573.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.failhard =
                         (uu___120_18573.FStar_TypeChecker_Env.failhard);
                       FStar_TypeChecker_Env.nosynth =
                         (uu___120_18573.FStar_TypeChecker_Env.nosynth);
                       FStar_TypeChecker_Env.tc_term =
                         (uu___120_18573.FStar_TypeChecker_Env.tc_term);
                       FStar_TypeChecker_Env.type_of =
                         (uu___120_18573.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___120_18573.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___120_18573.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___120_18573.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___120_18573.FStar_TypeChecker_Env.proof_ns);
                       FStar_TypeChecker_Env.synth =
                         (uu___120_18573.FStar_TypeChecker_Env.synth);
                       FStar_TypeChecker_Env.is_native_tactic =
                         (uu___120_18573.FStar_TypeChecker_Env.is_native_tactic);
                       FStar_TypeChecker_Env.identifier_info =
                         (uu___120_18573.FStar_TypeChecker_Env.identifier_info);
                       FStar_TypeChecker_Env.tc_hooks =
                         (uu___120_18573.FStar_TypeChecker_Env.tc_hooks);
                       FStar_TypeChecker_Env.dsenv =
                         (uu___120_18573.FStar_TypeChecker_Env.dsenv);
                       FStar_TypeChecker_Env.dep_graph =
                         (uu___120_18573.FStar_TypeChecker_Env.dep_graph)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c  in
              let rec aux norm1 t_norm1 =
                let uu____18606 = FStar_Syntax_Util.abs_formals e  in
                match uu____18606 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____18670::uu____18671 ->
                         let uu____18686 =
                           let uu____18687 =
                             let uu____18690 =
                               FStar_Syntax_Subst.compress t_norm1  in
                             FStar_All.pipe_left FStar_Syntax_Util.unascribe
                               uu____18690
                              in
                           uu____18687.FStar_Syntax_Syntax.n  in
                         (match uu____18686 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____18733 =
                                FStar_Syntax_Subst.open_comp formals c  in
                              (match uu____18733 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1
                                      in
                                   let nbinders = FStar_List.length binders
                                      in
                                   let tres = get_result_type c1  in
                                   let uu____18775 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1)
                                      in
                                   if uu____18775
                                   then
                                     let uu____18810 =
                                       FStar_Util.first_N nformals binders
                                        in
                                     (match uu____18810 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____18904  ->
                                                   fun uu____18905  ->
                                                     match (uu____18904,
                                                             uu____18905)
                                                     with
                                                     | ((x,uu____18923),
                                                        (b,uu____18925)) ->
                                                         let uu____18934 =
                                                           let uu____18941 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b
                                                              in
                                                           (x, uu____18941)
                                                            in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____18934)
                                                formals1 bs0
                                               in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1
                                             in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt
                                             in
                                          let uu____18943 =
                                            let uu____18964 =
                                              get_result_type c2  in
                                            (bs0, body1, bs0, uu____18964)
                                             in
                                          (uu____18943, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____19032 =
                                          eta_expand1 binders formals1 body
                                            tres
                                           in
                                        match uu____19032 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____19121) ->
                              let uu____19126 =
                                let uu____19147 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort  in
                                FStar_Pervasives_Native.fst uu____19147  in
                              (uu____19126, true)
                          | uu____19212 when Prims.op_Negation norm1 ->
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
                          | uu____19214 ->
                              let uu____19215 =
                                let uu____19216 =
                                  FStar_Syntax_Print.term_to_string e  in
                                let uu____19217 =
                                  FStar_Syntax_Print.term_to_string t_norm1
                                   in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____19216
                                  uu____19217
                                 in
                              failwith uu____19215)
                     | uu____19242 ->
                         let rec aux' t_norm2 =
                           let uu____19267 =
                             let uu____19268 =
                               FStar_Syntax_Subst.compress t_norm2  in
                             uu____19268.FStar_Syntax_Syntax.n  in
                           match uu____19267 with
                           | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                               let uu____19309 =
                                 FStar_Syntax_Subst.open_comp formals c  in
                               (match uu____19309 with
                                | (formals1,c1) ->
                                    let tres = get_result_type c1  in
                                    let uu____19337 =
                                      eta_expand1 [] formals1 e tres  in
                                    (match uu____19337 with
                                     | (binders1,body1) ->
                                         ((binders1, body1, formals1, tres),
                                           false)))
                           | FStar_Syntax_Syntax.Tm_refine (bv,uu____19417)
                               -> aux' bv.FStar_Syntax_Syntax.sort
                           | uu____19422 -> (([], e, [], t_norm2), false)  in
                         aux' t_norm1)
                 in
              aux false t_norm  in
            (try
               let uu____19478 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp)))
                  in
               if uu____19478
               then encode_top_level_vals env bindings quals
               else
                 (let uu____19490 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____19584  ->
                            fun lb  ->
                              match uu____19584 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____19679 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    if uu____19679
                                    then FStar_Exn.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp
                                       in
                                    let uu____19682 =
                                      let uu____19697 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname
                                         in
                                      declare_top_level_let env1 uu____19697
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm
                                       in
                                    match uu____19682 with
                                    | (tok,decl,env2) ->
                                        let uu____19743 =
                                          let uu____19756 =
                                            let uu____19767 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname
                                               in
                                            (uu____19767, tok)  in
                                          uu____19756 :: toks  in
                                        (uu____19743, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env))
                     in
                  match uu____19490 with
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
                        | uu____19950 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____19958 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort)
                                      in
                                   mk_Apply uu____19958 vars)
                            else
                              (let uu____19960 =
                                 let uu____19967 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars
                                    in
                                 (f, uu____19967)  in
                               FStar_SMTEncoding_Util.mkApp uu____19960)
                         in
                      let encode_non_rec_lbdef bindings1 typs2 toks2 env2 =
                        match (bindings1, typs2, toks2) with
                        | ({ FStar_Syntax_Syntax.lbname = uu____20049;
                             FStar_Syntax_Syntax.lbunivs = uvs;
                             FStar_Syntax_Syntax.lbtyp = uu____20051;
                             FStar_Syntax_Syntax.lbeff = uu____20052;
                             FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                           (flid_fv,(f,ftok))::[]) ->
                            let flid =
                              (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                               in
                            let uu____20115 =
                              let uu____20122 =
                                FStar_TypeChecker_Env.open_universes_in
                                  env2.tcenv uvs [e; t_norm]
                                 in
                              match uu____20122 with
                              | (tcenv',uu____20140,e_t) ->
                                  let uu____20146 =
                                    match e_t with
                                    | e1::t_norm1::[] -> (e1, t_norm1)
                                    | uu____20157 -> failwith "Impossible"
                                     in
                                  (match uu____20146 with
                                   | (e1,t_norm1) ->
                                       ((let uu___123_20173 = env2  in
                                         {
                                           bindings =
                                             (uu___123_20173.bindings);
                                           depth = (uu___123_20173.depth);
                                           tcenv = tcenv';
                                           warn = (uu___123_20173.warn);
                                           cache = (uu___123_20173.cache);
                                           nolabels =
                                             (uu___123_20173.nolabels);
                                           use_zfuel_name =
                                             (uu___123_20173.use_zfuel_name);
                                           encode_non_total_function_typ =
                                             (uu___123_20173.encode_non_total_function_typ);
                                           current_module_name =
                                             (uu___123_20173.current_module_name)
                                         }), e1, t_norm1))
                               in
                            (match uu____20115 with
                             | (env',e1,t_norm1) ->
                                 let uu____20183 =
                                   destruct_bound_function flid t_norm1 e1
                                    in
                                 (match uu____20183 with
                                  | ((binders,body,uu____20204,uu____20205),curry)
                                      ->
                                      ((let uu____20216 =
                                          FStar_All.pipe_left
                                            (FStar_TypeChecker_Env.debug
                                               env2.tcenv)
                                            (FStar_Options.Other
                                               "SMTEncoding")
                                           in
                                        if uu____20216
                                        then
                                          let uu____20217 =
                                            FStar_Syntax_Print.binders_to_string
                                              ", " binders
                                             in
                                          let uu____20218 =
                                            FStar_Syntax_Print.term_to_string
                                              body
                                             in
                                          FStar_Util.print2
                                            "Encoding let : binders=[%s], body=%s\n"
                                            uu____20217 uu____20218
                                        else ());
                                       (let uu____20220 =
                                          encode_binders
                                            FStar_Pervasives_Native.None
                                            binders env'
                                           in
                                        match uu____20220 with
                                        | (vars,guards,env'1,binder_decls,uu____20247)
                                            ->
                                            let body1 =
                                              let uu____20261 =
                                                FStar_TypeChecker_Env.is_reifiable_function
                                                  env'1.tcenv t_norm1
                                                 in
                                              if uu____20261
                                              then
                                                FStar_TypeChecker_Util.reify_body
                                                  env'1.tcenv body
                                              else body  in
                                            let app =
                                              mk_app1 curry f ftok vars  in
                                            let uu____20264 =
                                              let uu____20273 =
                                                FStar_All.pipe_right quals
                                                  (FStar_List.contains
                                                     FStar_Syntax_Syntax.Logic)
                                                 in
                                              if uu____20273
                                              then
                                                let uu____20284 =
                                                  FStar_SMTEncoding_Term.mk_Valid
                                                    app
                                                   in
                                                let uu____20285 =
                                                  encode_formula body1 env'1
                                                   in
                                                (uu____20284, uu____20285)
                                              else
                                                (let uu____20295 =
                                                   encode_term body1 env'1
                                                    in
                                                 (app, uu____20295))
                                               in
                                            (match uu____20264 with
                                             | (app1,(body2,decls2)) ->
                                                 let eqn =
                                                   let uu____20318 =
                                                     let uu____20325 =
                                                       let uu____20326 =
                                                         let uu____20337 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (app1, body2)
                                                            in
                                                         ([[app1]], vars,
                                                           uu____20337)
                                                          in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____20326
                                                        in
                                                     let uu____20348 =
                                                       let uu____20351 =
                                                         FStar_Util.format1
                                                           "Equation for %s"
                                                           flid.FStar_Ident.str
                                                          in
                                                       FStar_Pervasives_Native.Some
                                                         uu____20351
                                                        in
                                                     (uu____20325,
                                                       uu____20348,
                                                       (Prims.strcat
                                                          "equation_" f))
                                                      in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____20318
                                                    in
                                                 let uu____20354 =
                                                   let uu____20357 =
                                                     let uu____20360 =
                                                       let uu____20363 =
                                                         let uu____20366 =
                                                           primitive_type_axioms
                                                             env2.tcenv flid
                                                             f app1
                                                            in
                                                         FStar_List.append
                                                           [eqn] uu____20366
                                                          in
                                                       FStar_List.append
                                                         decls2 uu____20363
                                                        in
                                                     FStar_List.append
                                                       binder_decls
                                                       uu____20360
                                                      in
                                                   FStar_List.append decls1
                                                     uu____20357
                                                    in
                                                 (uu____20354, env2))))))
                        | uu____20371 -> failwith "Impossible"  in
                      let encode_rec_lbdefs bindings1 typs2 toks2 env2 =
                        let fuel =
                          let uu____20456 = varops.fresh "fuel"  in
                          (uu____20456, FStar_SMTEncoding_Term.Fuel_sort)  in
                        let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel  in
                        let env0 = env2  in
                        let uu____20459 =
                          FStar_All.pipe_right toks2
                            (FStar_List.fold_left
                               (fun uu____20547  ->
                                  fun uu____20548  ->
                                    match (uu____20547, uu____20548) with
                                    | ((gtoks,env3),(flid_fv,(f,ftok))) ->
                                        let flid =
                                          (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                           in
                                        let g =
                                          let uu____20696 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented"
                                             in
                                          varops.new_fvar uu____20696  in
                                        let gtok =
                                          let uu____20698 =
                                            FStar_Ident.lid_add_suffix flid
                                              "fuel_instrumented_token"
                                             in
                                          varops.new_fvar uu____20698  in
                                        let env4 =
                                          let uu____20700 =
                                            let uu____20703 =
                                              FStar_SMTEncoding_Util.mkApp
                                                (g, [fuel_tm])
                                               in
                                            FStar_All.pipe_left
                                              (fun _0_43  ->
                                                 FStar_Pervasives_Native.Some
                                                   _0_43) uu____20703
                                             in
                                          push_free_var env3 flid gtok
                                            uu____20700
                                           in
                                        (((flid, f, ftok, g, gtok) :: gtoks),
                                          env4)) ([], env2))
                           in
                        match uu____20459 with
                        | (gtoks,env3) ->
                            let gtoks1 = FStar_List.rev gtoks  in
                            let encode_one_binding env01 uu____20859 t_norm
                              uu____20861 =
                              match (uu____20859, uu____20861) with
                              | ((flid,f,ftok,g,gtok),{
                                                        FStar_Syntax_Syntax.lbname
                                                          = lbn;
                                                        FStar_Syntax_Syntax.lbunivs
                                                          = uvs;
                                                        FStar_Syntax_Syntax.lbtyp
                                                          = uu____20905;
                                                        FStar_Syntax_Syntax.lbeff
                                                          = uu____20906;
                                                        FStar_Syntax_Syntax.lbdef
                                                          = e;_})
                                  ->
                                  let uu____20934 =
                                    let uu____20941 =
                                      FStar_TypeChecker_Env.open_universes_in
                                        env3.tcenv uvs [e; t_norm]
                                       in
                                    match uu____20941 with
                                    | (tcenv',uu____20963,e_t) ->
                                        let uu____20969 =
                                          match e_t with
                                          | e1::t_norm1::[] -> (e1, t_norm1)
                                          | uu____20980 ->
                                              failwith "Impossible"
                                           in
                                        (match uu____20969 with
                                         | (e1,t_norm1) ->
                                             ((let uu___124_20996 = env3  in
                                               {
                                                 bindings =
                                                   (uu___124_20996.bindings);
                                                 depth =
                                                   (uu___124_20996.depth);
                                                 tcenv = tcenv';
                                                 warn = (uu___124_20996.warn);
                                                 cache =
                                                   (uu___124_20996.cache);
                                                 nolabels =
                                                   (uu___124_20996.nolabels);
                                                 use_zfuel_name =
                                                   (uu___124_20996.use_zfuel_name);
                                                 encode_non_total_function_typ
                                                   =
                                                   (uu___124_20996.encode_non_total_function_typ);
                                                 current_module_name =
                                                   (uu___124_20996.current_module_name)
                                               }), e1, t_norm1))
                                     in
                                  (match uu____20934 with
                                   | (env',e1,t_norm1) ->
                                       ((let uu____21011 =
                                           FStar_All.pipe_left
                                             (FStar_TypeChecker_Env.debug
                                                env01.tcenv)
                                             (FStar_Options.Other
                                                "SMTEncoding")
                                            in
                                         if uu____21011
                                         then
                                           let uu____21012 =
                                             FStar_Syntax_Print.lbname_to_string
                                               lbn
                                              in
                                           let uu____21013 =
                                             FStar_Syntax_Print.term_to_string
                                               t_norm1
                                              in
                                           let uu____21014 =
                                             FStar_Syntax_Print.term_to_string
                                               e1
                                              in
                                           FStar_Util.print3
                                             "Encoding let rec %s : %s = %s\n"
                                             uu____21012 uu____21013
                                             uu____21014
                                         else ());
                                        (let uu____21016 =
                                           destruct_bound_function flid
                                             t_norm1 e1
                                            in
                                         match uu____21016 with
                                         | ((binders,body,formals,tres),curry)
                                             ->
                                             ((let uu____21053 =
                                                 FStar_All.pipe_left
                                                   (FStar_TypeChecker_Env.debug
                                                      env01.tcenv)
                                                   (FStar_Options.Other
                                                      "SMTEncoding")
                                                  in
                                               if uu____21053
                                               then
                                                 let uu____21054 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " binders
                                                    in
                                                 let uu____21055 =
                                                   FStar_Syntax_Print.term_to_string
                                                     body
                                                    in
                                                 let uu____21056 =
                                                   FStar_Syntax_Print.binders_to_string
                                                     ", " formals
                                                    in
                                                 let uu____21057 =
                                                   FStar_Syntax_Print.term_to_string
                                                     tres
                                                    in
                                                 FStar_Util.print4
                                                   "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                   uu____21054 uu____21055
                                                   uu____21056 uu____21057
                                               else ());
                                              if curry
                                              then
                                                failwith
                                                  "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                              else ();
                                              (let uu____21061 =
                                                 encode_binders
                                                   FStar_Pervasives_Native.None
                                                   binders env'
                                                  in
                                               match uu____21061 with
                                               | (vars,guards,env'1,binder_decls,uu____21092)
                                                   ->
                                                   let decl_g =
                                                     let uu____21106 =
                                                       let uu____21117 =
                                                         let uu____21120 =
                                                           FStar_List.map
                                                             FStar_Pervasives_Native.snd
                                                             vars
                                                            in
                                                         FStar_SMTEncoding_Term.Fuel_sort
                                                           :: uu____21120
                                                          in
                                                       (g, uu____21117,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         (FStar_Pervasives_Native.Some
                                                            "Fuel-instrumented function name"))
                                                        in
                                                     FStar_SMTEncoding_Term.DeclFun
                                                       uu____21106
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
                                                     let uu____21145 =
                                                       let uu____21152 =
                                                         FStar_List.map
                                                           FStar_SMTEncoding_Util.mkFreeV
                                                           vars
                                                          in
                                                       (f, uu____21152)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21145
                                                      in
                                                   let gsapp =
                                                     let uu____21162 =
                                                       let uu____21169 =
                                                         let uu____21172 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("SFuel",
                                                               [fuel_tm])
                                                            in
                                                         uu____21172 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21169)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21162
                                                      in
                                                   let gmax =
                                                     let uu____21178 =
                                                       let uu____21185 =
                                                         let uu____21188 =
                                                           FStar_SMTEncoding_Util.mkApp
                                                             ("MaxFuel", [])
                                                            in
                                                         uu____21188 ::
                                                           vars_tm
                                                          in
                                                       (g, uu____21185)  in
                                                     FStar_SMTEncoding_Util.mkApp
                                                       uu____21178
                                                      in
                                                   let body1 =
                                                     let uu____21194 =
                                                       FStar_TypeChecker_Env.is_reifiable_function
                                                         env'1.tcenv t_norm1
                                                        in
                                                     if uu____21194
                                                     then
                                                       FStar_TypeChecker_Util.reify_body
                                                         env'1.tcenv body
                                                     else body  in
                                                   let uu____21196 =
                                                     encode_term body1 env'1
                                                      in
                                                   (match uu____21196 with
                                                    | (body_tm,decls2) ->
                                                        let eqn_g =
                                                          let uu____21214 =
                                                            let uu____21221 =
                                                              let uu____21222
                                                                =
                                                                let uu____21237
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
                                                                  uu____21237)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall'
                                                                uu____21222
                                                               in
                                                            let uu____21258 =
                                                              let uu____21261
                                                                =
                                                                FStar_Util.format1
                                                                  "Equation for fuel-instrumented recursive function: %s"
                                                                  flid.FStar_Ident.str
                                                                 in
                                                              FStar_Pervasives_Native.Some
                                                                uu____21261
                                                               in
                                                            (uu____21221,
                                                              uu____21258,
                                                              (Prims.strcat
                                                                 "equation_with_fuel_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21214
                                                           in
                                                        let eqn_f =
                                                          let uu____21265 =
                                                            let uu____21272 =
                                                              let uu____21273
                                                                =
                                                                let uu____21284
                                                                  =
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax)
                                                                   in
                                                                ([[app]],
                                                                  vars,
                                                                  uu____21284)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21273
                                                               in
                                                            (uu____21272,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Correspondence of recursive function to instrumented version"),
                                                              (Prims.strcat
                                                                 "@fuel_correspondence_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21265
                                                           in
                                                        let eqn_g' =
                                                          let uu____21298 =
                                                            let uu____21305 =
                                                              let uu____21306
                                                                =
                                                                let uu____21317
                                                                  =
                                                                  let uu____21318
                                                                    =
                                                                    let uu____21323
                                                                    =
                                                                    let uu____21324
                                                                    =
                                                                    let uu____21331
                                                                    =
                                                                    let uu____21334
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int "0")
                                                                     in
                                                                    uu____21334
                                                                    ::
                                                                    vars_tm
                                                                     in
                                                                    (g,
                                                                    uu____21331)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____21324
                                                                     in
                                                                    (gsapp,
                                                                    uu____21323)
                                                                     in
                                                                  FStar_SMTEncoding_Util.mkEq
                                                                    uu____21318
                                                                   in
                                                                ([[gsapp]],
                                                                  (fuel ::
                                                                  vars),
                                                                  uu____21317)
                                                                 in
                                                              FStar_SMTEncoding_Util.mkForall
                                                                uu____21306
                                                               in
                                                            (uu____21305,
                                                              (FStar_Pervasives_Native.Some
                                                                 "Fuel irrelevance"),
                                                              (Prims.strcat
                                                                 "@fuel_irrelevance_"
                                                                 g))
                                                             in
                                                          FStar_SMTEncoding_Util.mkAssume
                                                            uu____21298
                                                           in
                                                        let uu____21357 =
                                                          let uu____21366 =
                                                            encode_binders
                                                              FStar_Pervasives_Native.None
                                                              formals env02
                                                             in
                                                          match uu____21366
                                                          with
                                                          | (vars1,v_guards,env4,binder_decls1,uu____21395)
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
                                                                  let uu____21420
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                  mk_Apply
                                                                    uu____21420
                                                                    (fuel ::
                                                                    vars1)
                                                                   in
                                                                let uu____21425
                                                                  =
                                                                  let uu____21432
                                                                    =
                                                                    let uu____21433
                                                                    =
                                                                    let uu____21444
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp)  in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21444)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21433
                                                                     in
                                                                  (uu____21432,
                                                                    (
                                                                    FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (
                                                                    Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok))
                                                                   in
                                                                FStar_SMTEncoding_Util.mkAssume
                                                                  uu____21425
                                                                 in
                                                              let uu____21465
                                                                =
                                                                let uu____21472
                                                                  =
                                                                  encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env4
                                                                    gapp
                                                                   in
                                                                match uu____21472
                                                                with
                                                                | (g_typing,d3)
                                                                    ->
                                                                    let uu____21485
                                                                    =
                                                                    let uu____21488
                                                                    =
                                                                    let uu____21489
                                                                    =
                                                                    let uu____21496
                                                                    =
                                                                    let uu____21497
                                                                    =
                                                                    let uu____21508
                                                                    =
                                                                    let uu____21509
                                                                    =
                                                                    let uu____21514
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards
                                                                     in
                                                                    (uu____21514,
                                                                    g_typing)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____21509
                                                                     in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____21508)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____21497
                                                                     in
                                                                    (uu____21496,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g))  in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____21489
                                                                     in
                                                                    [uu____21488]
                                                                     in
                                                                    (d3,
                                                                    uu____21485)
                                                                 in
                                                              (match uu____21465
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
                                                        (match uu____21357
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
                            let uu____21579 =
                              let uu____21592 =
                                FStar_List.zip3 gtoks1 typs2 bindings1  in
                              FStar_List.fold_left
                                (fun uu____21671  ->
                                   fun uu____21672  ->
                                     match (uu____21671, uu____21672) with
                                     | ((decls2,eqns,env01),(gtok,ty,lb)) ->
                                         let uu____21827 =
                                           encode_one_binding env01 gtok ty
                                             lb
                                            in
                                         (match uu____21827 with
                                          | (decls',eqns',env02) ->
                                              ((decls' :: decls2),
                                                (FStar_List.append eqns' eqns),
                                                env02))) ([decls1], [], env0)
                                uu____21592
                               in
                            (match uu____21579 with
                             | (decls2,eqns,env01) ->
                                 let uu____21900 =
                                   let isDeclFun uu___90_21912 =
                                     match uu___90_21912 with
                                     | FStar_SMTEncoding_Term.DeclFun
                                         uu____21913 -> true
                                     | uu____21924 -> false  in
                                   let uu____21925 =
                                     FStar_All.pipe_right decls2
                                       FStar_List.flatten
                                      in
                                   FStar_All.pipe_right uu____21925
                                     (FStar_List.partition isDeclFun)
                                    in
                                 (match uu____21900 with
                                  | (prefix_decls,rest) ->
                                      let eqns1 = FStar_List.rev eqns  in
                                      ((FStar_List.append prefix_decls
                                          (FStar_List.append rest eqns1)),
                                        env01)))
                         in
                      let uu____21965 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___91_21969  ->
                                 match uu___91_21969 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____21970 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____21976 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t)
                                      in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____21976)))
                         in
                      if uu____21965
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
                   let uu____22028 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname))
                      in
                   FStar_All.pipe_right uu____22028
                     (FStar_String.concat " and ")
                    in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg)
                    in
                 ([decl], env))
  
let rec (encode_sigelt :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____22077 = FStar_Syntax_Util.lid_of_sigelt se  in
        match uu____22077 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str  in
      let uu____22081 = encode_sigelt' env se  in
      match uu____22081 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____22097 =
                  let uu____22098 = FStar_Util.format1 "<Skipped %s/>" nm  in
                  FStar_SMTEncoding_Term.Caption uu____22098  in
                [uu____22097]
            | uu____22099 ->
                let uu____22100 =
                  let uu____22103 =
                    let uu____22104 =
                      FStar_Util.format1 "<Start encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22104  in
                  uu____22103 :: g  in
                let uu____22105 =
                  let uu____22108 =
                    let uu____22109 =
                      FStar_Util.format1 "</end encoding %s>" nm  in
                    FStar_SMTEncoding_Term.Caption uu____22109  in
                  [uu____22108]  in
                FStar_List.append uu____22100 uu____22105
             in
          (g1, env1)

and (encode_sigelt' :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let is_opaque_to_smt t =
        let uu____22122 =
          let uu____22123 = FStar_Syntax_Subst.compress t  in
          uu____22123.FStar_Syntax_Syntax.n  in
        match uu____22122 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22127)) -> s = "opaque_to_smt"
        | uu____22128 -> false  in
      let is_uninterpreted_by_smt t =
        let uu____22133 =
          let uu____22134 = FStar_Syntax_Subst.compress t  in
          uu____22134.FStar_Syntax_Syntax.n  in
        match uu____22133 with
        | FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_string
            (s,uu____22138)) -> s = "uninterpreted_by_smt"
        | uu____22139 -> false  in
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____22144 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____22149 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____22152 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____22155 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____22170 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____22174 =
            let uu____22175 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable)
               in
            FStar_All.pipe_right uu____22175 Prims.op_Negation  in
          if uu____22174
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____22201 ->
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
               let uu____22221 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name
                  in
               match uu____22221 with
               | (aname,atok,env2) ->
                   let uu____22237 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ
                      in
                   (match uu____22237 with
                    | (formals,uu____22255) ->
                        let uu____22268 =
                          let uu____22273 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn
                             in
                          encode_term uu____22273 env2  in
                        (match uu____22268 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____22285 =
                                 let uu____22286 =
                                   let uu____22297 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____22313  ->
                                             FStar_SMTEncoding_Term.Term_sort))
                                      in
                                   (aname, uu____22297,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action"))
                                    in
                                 FStar_SMTEncoding_Term.DeclFun uu____22286
                                  in
                               [uu____22285;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))]
                                in
                             let uu____22326 =
                               let aux uu____22378 uu____22379 =
                                 match (uu____22378, uu____22379) with
                                 | ((bv,uu____22431),(env3,acc_sorts,acc)) ->
                                     let uu____22469 = gen_term_var env3 bv
                                        in
                                     (match uu____22469 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc)))
                                  in
                               FStar_List.fold_right aux formals
                                 (env2, [], [])
                                in
                             (match uu____22326 with
                              | (uu____22541,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs)
                                     in
                                  let a_eq =
                                    let uu____22564 =
                                      let uu____22571 =
                                        let uu____22572 =
                                          let uu____22583 =
                                            let uu____22584 =
                                              let uu____22589 =
                                                mk_Apply tm xs_sorts  in
                                              (app, uu____22589)  in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____22584
                                             in
                                          ([[app]], xs_sorts, uu____22583)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22572
                                         in
                                      (uu____22571,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22564
                                     in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort)
                                       in
                                    let tok_app = mk_Apply tok_term xs_sorts
                                       in
                                    let uu____22609 =
                                      let uu____22616 =
                                        let uu____22617 =
                                          let uu____22628 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app)
                                             in
                                          ([[tok_app]], xs_sorts,
                                            uu____22628)
                                           in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____22617
                                         in
                                      (uu____22616,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence"))
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____22609
                                     in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence]))))))
                in
             let uu____22647 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions
                in
             match uu____22647 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22675,uu____22676)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____22677 = new_term_constant_and_tok_from_lid env lid  in
          (match uu____22677 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____22694,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let will_encode_definition =
            let uu____22700 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___92_22704  ->
                      match uu___92_22704 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____22705 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____22710 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____22711 -> false))
               in
            Prims.op_Negation uu____22700  in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None
                in
             let uu____22720 =
               let uu____22727 =
                 FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
                   (FStar_Util.for_some is_uninterpreted_by_smt)
                  in
               encode_top_level_val uu____22727 env fv t quals  in
             match uu____22720 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str  in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort)
                    in
                 let uu____22742 =
                   let uu____22745 =
                     primitive_type_axioms env1.tcenv lid tname tsym  in
                   FStar_List.append decls uu____22745  in
                 (uu____22742, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____22753 = FStar_Syntax_Subst.open_univ_vars us f  in
          (match uu____22753 with
           | (uu____22762,f1) ->
               let uu____22764 = encode_formula f1 env  in
               (match uu____22764 with
                | (f2,decls) ->
                    let g =
                      let uu____22778 =
                        let uu____22779 =
                          let uu____22786 =
                            let uu____22789 =
                              let uu____22790 =
                                FStar_Syntax_Print.lid_to_string l  in
                              FStar_Util.format1 "Assumption: %s" uu____22790
                               in
                            FStar_Pervasives_Native.Some uu____22789  in
                          let uu____22791 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str)
                             in
                          (f2, uu____22786, uu____22791)  in
                        FStar_SMTEncoding_Util.mkAssume uu____22779  in
                      [uu____22778]  in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____22797) when
          (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
             (FStar_List.contains FStar_Syntax_Syntax.Irreducible))
            ||
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigattrs
               (FStar_Util.for_some is_opaque_to_smt))
          ->
          let attrs = se.FStar_Syntax_Syntax.sigattrs  in
          let uu____22809 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____22827 =
                       let uu____22830 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
                       uu____22830.FStar_Syntax_Syntax.fv_name  in
                     uu____22827.FStar_Syntax_Syntax.v  in
                   let uu____22831 =
                     let uu____22832 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid
                        in
                     FStar_All.pipe_left FStar_Option.isNone uu____22832  in
                   if uu____22831
                   then
                     let val_decl =
                       let uu___127_22860 = se  in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___127_22860.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (FStar_Syntax_Syntax.Irreducible ::
                           (se.FStar_Syntax_Syntax.sigquals));
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___127_22860.FStar_Syntax_Syntax.sigmeta);
                         FStar_Syntax_Syntax.sigattrs =
                           (uu___127_22860.FStar_Syntax_Syntax.sigattrs)
                       }  in
                     let uu____22865 = encode_sigelt' env1 val_decl  in
                     match uu____22865 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs)
             in
          (match uu____22809 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____22893,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____22895;
                          FStar_Syntax_Syntax.lbtyp = uu____22896;
                          FStar_Syntax_Syntax.lbeff = uu____22897;
                          FStar_Syntax_Syntax.lbdef = uu____22898;_}::[]),uu____22899)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____22918 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
             in
          (match uu____22918 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort)  in
               let x = FStar_SMTEncoding_Util.mkFreeV xx  in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x])
                  in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x])  in
               let decls =
                 let uu____22947 =
                   let uu____22950 =
                     let uu____22951 =
                       let uu____22958 =
                         let uu____22959 =
                           let uu____22970 =
                             let uu____22971 =
                               let uu____22976 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ((FStar_Pervasives_Native.snd
                                       FStar_SMTEncoding_Term.boxBoolFun),
                                     [x])
                                  in
                               (valid_b2t_x, uu____22976)  in
                             FStar_SMTEncoding_Util.mkEq uu____22971  in
                           ([[b2t_x]], [xx], uu____22970)  in
                         FStar_SMTEncoding_Util.mkForall uu____22959  in
                       (uu____22958,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def")
                        in
                     FStar_SMTEncoding_Util.mkAssume uu____22951  in
                   [uu____22950]  in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____22947
                  in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____23009,uu____23010) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___93_23019  ->
                  match uu___93_23019 with
                  | FStar_Syntax_Syntax.Discriminator uu____23020 -> true
                  | uu____23021 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____23024,lids) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____23035 =
                     let uu____23036 = FStar_List.hd l.FStar_Ident.ns  in
                     uu____23036.FStar_Ident.idText  in
                   uu____23035 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___94_23040  ->
                     match uu___94_23040 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____23041 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____23045) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___95_23062  ->
                  match uu___95_23062 with
                  | FStar_Syntax_Syntax.Projector uu____23063 -> true
                  | uu____23068 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname  in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v  in
          let uu____23071 = try_lookup_free_var env l  in
          (match uu____23071 with
           | FStar_Pervasives_Native.Some uu____23078 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___128_23082 = se  in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___128_23082.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___128_23082.FStar_Syntax_Syntax.sigmeta);
                   FStar_Syntax_Syntax.sigattrs =
                     (uu___128_23082.FStar_Syntax_Syntax.sigattrs)
                 }  in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let ((is_rec,bindings),uu____23089) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____23107) ->
          let uu____23116 = encode_sigelts env ses  in
          (match uu____23116 with
           | (g,env1) ->
               let uu____23133 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___96_23156  ->
                         match uu___96_23156 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____23157;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____23158;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____23159;_}
                             -> false
                         | uu____23162 -> true))
                  in
               (match uu____23133 with
                | (g',inversions) ->
                    let uu____23177 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___97_23198  ->
                              match uu___97_23198 with
                              | FStar_SMTEncoding_Term.DeclFun uu____23199 ->
                                  true
                              | uu____23210 -> false))
                       in
                    (match uu____23177 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____23228,tps,k,uu____23231,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___98_23248  ->
                    match uu___98_23248 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____23249 -> false))
             in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____23258 = c  in
              match uu____23258 with
              | (name,args,uu____23263,uu____23264,uu____23265) ->
                  let uu____23270 =
                    let uu____23271 =
                      let uu____23282 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____23299  ->
                                match uu____23299 with
                                | (uu____23306,sort,uu____23308) -> sort))
                         in
                      (name, uu____23282, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None)
                       in
                    FStar_SMTEncoding_Term.DeclFun uu____23271  in
                  [uu____23270]
            else FStar_SMTEncoding_Term.constructor_to_decl c  in
          let inversion_axioms tapp vars =
            let uu____23335 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____23341 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l  in
                      FStar_All.pipe_right uu____23341 FStar_Option.isNone))
               in
            if uu____23335
            then []
            else
              (let uu____23373 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort  in
               match uu____23373 with
               | (xxsym,xx) ->
                   let uu____23382 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____23421  ->
                             fun l  ->
                               match uu____23421 with
                               | (out,decls) ->
                                   let uu____23441 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l
                                      in
                                   (match uu____23441 with
                                    | (uu____23452,data_t) ->
                                        let uu____23454 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t
                                           in
                                        (match uu____23454 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____23500 =
                                                 let uu____23501 =
                                                   FStar_Syntax_Subst.compress
                                                     res
                                                    in
                                                 uu____23501.FStar_Syntax_Syntax.n
                                                  in
                                               match uu____23500 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____23512,indices) ->
                                                   indices
                                               | uu____23534 -> []  in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____23558  ->
                                                         match uu____23558
                                                         with
                                                         | (x,uu____23564) ->
                                                             let uu____23565
                                                               =
                                                               let uu____23566
                                                                 =
                                                                 let uu____23573
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x
                                                                    in
                                                                 (uu____23573,
                                                                   [xx])
                                                                  in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____23566
                                                                in
                                                             push_term_var
                                                               env1 x
                                                               uu____23565)
                                                    env)
                                                in
                                             let uu____23576 =
                                               encode_args indices env1  in
                                             (match uu____23576 with
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
                                                      let uu____23602 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____23618
                                                                 =
                                                                 let uu____23623
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1
                                                                    in
                                                                 (uu____23623,
                                                                   a)
                                                                  in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____23618)
                                                          vars indices1
                                                         in
                                                      FStar_All.pipe_right
                                                        uu____23602
                                                        FStar_SMTEncoding_Util.mk_and_l
                                                       in
                                                    let uu____23626 =
                                                      let uu____23627 =
                                                        let uu____23632 =
                                                          let uu____23633 =
                                                            let uu____23638 =
                                                              mk_data_tester
                                                                env1 l xx
                                                               in
                                                            (uu____23638,
                                                              eqs)
                                                             in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____23633
                                                           in
                                                        (out, uu____23632)
                                                         in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____23627
                                                       in
                                                    (uu____23626,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, []))
                      in
                   (match uu____23382 with
                    | (data_ax,decls) ->
                        let uu____23651 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                        (match uu____23651 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____23662 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff])
                                      in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____23662 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp
                                  in
                               let uu____23666 =
                                 let uu____23673 =
                                   let uu____23674 =
                                     let uu____23685 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars)
                                        in
                                     let uu____23700 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax)
                                        in
                                     ([[xx_has_type_sfuel]], uu____23685,
                                       uu____23700)
                                      in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____23674
                                    in
                                 let uu____23715 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str)
                                    in
                                 (uu____23673,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____23715)
                                  in
                               FStar_SMTEncoding_Util.mkAssume uu____23666
                                in
                             FStar_List.append decls [fuel_guarded_inversion])))
             in
          let uu____23718 =
            let uu____23731 =
              let uu____23732 = FStar_Syntax_Subst.compress k  in
              uu____23732.FStar_Syntax_Syntax.n  in
            match uu____23731 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____23777 -> (tps, k)  in
          (match uu____23718 with
           | (formals,res) ->
               let uu____23800 = FStar_Syntax_Subst.open_term formals res  in
               (match uu____23800 with
                | (formals1,res1) ->
                    let uu____23811 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env
                       in
                    (match uu____23811 with
                     | (vars,guards,env',binder_decls,uu____23836) ->
                         let uu____23849 =
                           new_term_constant_and_tok_from_lid env t  in
                         (match uu____23849 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, [])  in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards  in
                              let tapp =
                                let uu____23868 =
                                  let uu____23875 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars
                                     in
                                  (tname, uu____23875)  in
                                FStar_SMTEncoding_Util.mkApp uu____23868  in
                              let uu____23884 =
                                let tname_decl =
                                  let uu____23894 =
                                    let uu____23895 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____23927  ->
                                              match uu____23927 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false)))
                                       in
                                    let uu____23940 = varops.next_id ()  in
                                    (tname, uu____23895,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____23940, false)
                                     in
                                  constructor_or_logic_type_decl uu____23894
                                   in
                                let uu____23949 =
                                  match vars with
                                  | [] ->
                                      let uu____23962 =
                                        let uu____23963 =
                                          let uu____23966 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, [])
                                             in
                                          FStar_All.pipe_left
                                            (fun _0_44  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_44) uu____23966
                                           in
                                        push_free_var env1 t tname
                                          uu____23963
                                         in
                                      ([], uu____23962)
                                  | uu____23973 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token"))
                                         in
                                      let ttok_fresh =
                                        let uu____23982 = varops.next_id ()
                                           in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____23982
                                         in
                                      let ttok_app = mk_Apply ttok_tm vars
                                         in
                                      let pats = [[ttok_app]; [tapp]]  in
                                      let name_tok_corr =
                                        let uu____23996 =
                                          let uu____24003 =
                                            let uu____24004 =
                                              let uu____24019 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp)
                                                 in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____24019)
                                               in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____24004
                                             in
                                          (uu____24003,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok))
                                           in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____23996
                                         in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1)
                                   in
                                match uu____23949 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2)
                                 in
                              (match uu____23884 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____24059 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp
                                        in
                                     match uu____24059 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____24077 =
                                               let uu____24078 =
                                                 let uu____24085 =
                                                   let uu____24086 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm
                                                      in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____24086
                                                    in
                                                 (uu____24085,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24078
                                                in
                                             [uu____24077]
                                           else []  in
                                         let uu____24090 =
                                           let uu____24093 =
                                             let uu____24096 =
                                               let uu____24097 =
                                                 let uu____24104 =
                                                   let uu____24105 =
                                                     let uu____24116 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1)
                                                        in
                                                     ([[tapp]], vars,
                                                       uu____24116)
                                                      in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____24105
                                                    in
                                                 (uu____24104,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok))
                                                  in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____24097
                                                in
                                             [uu____24096]  in
                                           FStar_List.append karr uu____24093
                                            in
                                         FStar_List.append decls1 uu____24090
                                      in
                                   let aux =
                                     let uu____24132 =
                                       let uu____24135 =
                                         inversion_axioms tapp vars  in
                                       let uu____24138 =
                                         let uu____24141 =
                                           pretype_axiom env2 tapp vars  in
                                         [uu____24141]  in
                                       FStar_List.append uu____24135
                                         uu____24138
                                        in
                                     FStar_List.append kindingAx uu____24132
                                      in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux)
                                      in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24148,uu____24149,uu____24150,uu____24151,uu____24152)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____24160,t,uu____24162,n_tps,uu____24164) ->
          let quals = se.FStar_Syntax_Syntax.sigquals  in
          let uu____24172 = new_term_constant_and_tok_from_lid env d  in
          (match uu____24172 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, [])  in
               let uu____24189 = FStar_Syntax_Util.arrow_formals t  in
               (match uu____24189 with
                | (formals,t_res) ->
                    let uu____24224 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort  in
                    (match uu____24224 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm])
                            in
                         let uu____24238 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1
                            in
                         (match uu____24238 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true  in
                                          let uu____24308 =
                                            mk_term_projector_name d x  in
                                          (uu____24308,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible)))
                                 in
                              let datacons =
                                let uu____24310 =
                                  let uu____24329 = varops.next_id ()  in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____24329, true)
                                   in
                                FStar_All.pipe_right uu____24310
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
                              let uu____24368 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm
                                 in
                              (match uu____24368 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____24380::uu____24381 ->
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
                                         let uu____24426 =
                                           let uu____24437 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing
                                              in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____24437)
                                            in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____24426
                                     | uu____24462 -> tok_typing  in
                                   let uu____24471 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1
                                      in
                                   (match uu____24471 with
                                    | (vars',guards',env'',decls_formals,uu____24496)
                                        ->
                                        let uu____24509 =
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
                                        (match uu____24509 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards'
                                                in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____24540 ->
                                                   let uu____24547 =
                                                     let uu____24548 =
                                                       varops.next_id ()  in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____24548
                                                      in
                                                   [uu____24547]
                                                in
                                             let encode_elim uu____24558 =
                                               let uu____24559 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res
                                                  in
                                               match uu____24559 with
                                               | (head1,args) ->
                                                   let uu____24602 =
                                                     let uu____24603 =
                                                       FStar_Syntax_Subst.compress
                                                         head1
                                                        in
                                                     uu____24603.FStar_Syntax_Syntax.n
                                                      in
                                                   (match uu____24602 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____24613;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____24614;_},uu____24615)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name
                                                           in
                                                        let uu____24621 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____24621
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
                                                                 | uu____24664
                                                                    ->
                                                                    let uu____24665
                                                                    =
                                                                    let uu____24670
                                                                    =
                                                                    let uu____24671
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____24671
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____24670)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____24665
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____24687
                                                                    =
                                                                    let uu____24688
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____24688
                                                                     in
                                                                    if
                                                                    uu____24687
                                                                    then
                                                                    let uu____24701
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____24701]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____24703
                                                               =
                                                               let uu____24716
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____24766
                                                                     ->
                                                                    fun
                                                                    uu____24767
                                                                     ->
                                                                    match 
                                                                    (uu____24766,
                                                                    uu____24767)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____24862
                                                                    =
                                                                    let uu____24869
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____24869
                                                                     in
                                                                    (match uu____24862
                                                                    with
                                                                    | 
                                                                    (uu____24882,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____24890
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____24890
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____24892
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____24892
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
                                                                 uu____24716
                                                                in
                                                             (match uu____24703
                                                              with
                                                              | (uu____24907,arg_vars,elim_eqns_or_guards,uu____24910)
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
                                                                    let uu____24940
                                                                    =
                                                                    let uu____24947
                                                                    =
                                                                    let uu____24948
                                                                    =
                                                                    let uu____24959
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____24970
                                                                    =
                                                                    let uu____24971
                                                                    =
                                                                    let uu____24976
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____24976)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____24971
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____24959,
                                                                    uu____24970)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____24948
                                                                     in
                                                                    (uu____24947,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____24940
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____24999
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____24999,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25001
                                                                    =
                                                                    let uu____25008
                                                                    =
                                                                    let uu____25009
                                                                    =
                                                                    let uu____25020
                                                                    =
                                                                    let uu____25025
                                                                    =
                                                                    let uu____25028
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25028]
                                                                     in
                                                                    [uu____25025]
                                                                     in
                                                                    let uu____25033
                                                                    =
                                                                    let uu____25034
                                                                    =
                                                                    let uu____25039
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25040
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25039,
                                                                    uu____25040)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25034
                                                                     in
                                                                    (uu____25020,
                                                                    [x],
                                                                    uu____25033)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25009
                                                                     in
                                                                    let uu____25059
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25008,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25059)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25001
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25066
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
                                                                    (let uu____25094
                                                                    =
                                                                    let uu____25095
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25095
                                                                    dapp1  in
                                                                    [uu____25094])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25066
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25102
                                                                    =
                                                                    let uu____25109
                                                                    =
                                                                    let uu____25110
                                                                    =
                                                                    let uu____25121
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25132
                                                                    =
                                                                    let uu____25133
                                                                    =
                                                                    let uu____25138
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25138)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25133
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25121,
                                                                    uu____25132)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25110
                                                                     in
                                                                    (uu____25109,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25102)
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
                                                        let uu____25159 =
                                                          encode_args args
                                                            env'
                                                           in
                                                        (match uu____25159
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
                                                                 | uu____25202
                                                                    ->
                                                                    let uu____25203
                                                                    =
                                                                    let uu____25208
                                                                    =
                                                                    let uu____25209
                                                                    =
                                                                    FStar_Syntax_Print.term_to_string
                                                                    orig_arg
                                                                     in
                                                                    FStar_Util.format1
                                                                    "Inductive type parameter %s must be a variable ; You may want to change it to an index."
                                                                    uu____25209
                                                                     in
                                                                    (FStar_Errors.Fatal_NonVariableInductiveTypeParameter,
                                                                    uu____25208)
                                                                     in
                                                                    FStar_Errors.raise_error
                                                                    uu____25203
                                                                    orig_arg.FStar_Syntax_Syntax.pos
                                                                  in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____25225
                                                                    =
                                                                    let uu____25226
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g  in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____25226
                                                                     in
                                                                    if
                                                                    uu____25225
                                                                    then
                                                                    let uu____25239
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv
                                                                     in
                                                                    [uu____25239]
                                                                    else []))
                                                                  in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1
                                                                in
                                                             let uu____25241
                                                               =
                                                               let uu____25254
                                                                 =
                                                                 FStar_List.zip
                                                                   args
                                                                   encoded_args
                                                                  in
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____25304
                                                                     ->
                                                                    fun
                                                                    uu____25305
                                                                     ->
                                                                    match 
                                                                    (uu____25304,
                                                                    uu____25305)
                                                                    with
                                                                    | 
                                                                    ((env2,arg_vars,eqns_or_guards,i),
                                                                    (orig_arg,arg))
                                                                    ->
                                                                    let uu____25400
                                                                    =
                                                                    let uu____25407
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun
                                                                     in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____25407
                                                                     in
                                                                    (match uu____25400
                                                                    with
                                                                    | 
                                                                    (uu____25420,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____25428
                                                                    =
                                                                    guards_for_parameter
                                                                    (FStar_Pervasives_Native.fst
                                                                    orig_arg)
                                                                    arg xv
                                                                     in
                                                                    uu____25428
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____25430
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv)
                                                                     in
                                                                    uu____25430
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
                                                                 uu____25254
                                                                in
                                                             (match uu____25241
                                                              with
                                                              | (uu____25445,arg_vars,elim_eqns_or_guards,uu____25448)
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
                                                                    let uu____25478
                                                                    =
                                                                    let uu____25485
                                                                    =
                                                                    let uu____25486
                                                                    =
                                                                    let uu____25497
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25508
                                                                    =
                                                                    let uu____25509
                                                                    =
                                                                    let uu____25514
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards)
                                                                     in
                                                                    (ty_pred,
                                                                    uu____25514)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25509
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25497,
                                                                    uu____25508)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25486
                                                                     in
                                                                    (uu____25485,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25478
                                                                     in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____25537
                                                                    =
                                                                    varops.fresh
                                                                    "x"  in
                                                                    (uu____25537,
                                                                    FStar_SMTEncoding_Term.Term_sort)
                                                                     in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x  in
                                                                    let uu____25539
                                                                    =
                                                                    let uu____25546
                                                                    =
                                                                    let uu____25547
                                                                    =
                                                                    let uu____25558
                                                                    =
                                                                    let uu____25563
                                                                    =
                                                                    let uu____25566
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    [uu____25566]
                                                                     in
                                                                    [uu____25563]
                                                                     in
                                                                    let uu____25571
                                                                    =
                                                                    let uu____25572
                                                                    =
                                                                    let uu____25577
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm  in
                                                                    let uu____25578
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1
                                                                     in
                                                                    (uu____25577,
                                                                    uu____25578)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25572
                                                                     in
                                                                    (uu____25558,
                                                                    [x],
                                                                    uu____25571)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25547
                                                                     in
                                                                    let uu____25597
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop"
                                                                     in
                                                                    (uu____25546,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____25597)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25539
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____25604
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
                                                                    (let uu____25632
                                                                    =
                                                                    let uu____25633
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1  in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____25633
                                                                    dapp1  in
                                                                    [uu____25632])))
                                                                     in
                                                                    FStar_All.pipe_right
                                                                    uu____25604
                                                                    FStar_List.flatten
                                                                     in
                                                                    let uu____25640
                                                                    =
                                                                    let uu____25647
                                                                    =
                                                                    let uu____25648
                                                                    =
                                                                    let uu____25659
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders)
                                                                     in
                                                                    let uu____25670
                                                                    =
                                                                    let uu____25671
                                                                    =
                                                                    let uu____25676
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec  in
                                                                    (ty_pred,
                                                                    uu____25676)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____25671
                                                                     in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____25659,
                                                                    uu____25670)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25648
                                                                     in
                                                                    (uu____25647,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25640)
                                                                     in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____25695 ->
                                                        ((let uu____25697 =
                                                            let uu____25702 =
                                                              let uu____25703
                                                                =
                                                                FStar_Syntax_Print.lid_to_string
                                                                  d
                                                                 in
                                                              let uu____25704
                                                                =
                                                                FStar_Syntax_Print.term_to_string
                                                                  head1
                                                                 in
                                                              FStar_Util.format2
                                                                "Constructor %s builds an unexpected type %s\n"
                                                                uu____25703
                                                                uu____25704
                                                               in
                                                            (FStar_Errors.Warning_ConstructorBuildsUnexpectedType,
                                                              uu____25702)
                                                             in
                                                          FStar_Errors.log_issue
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____25697);
                                                         ([], [])))
                                                in
                                             let uu____25709 = encode_elim ()
                                                in
                                             (match uu____25709 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____25729 =
                                                      let uu____25732 =
                                                        let uu____25735 =
                                                          let uu____25738 =
                                                            let uu____25741 =
                                                              let uu____25742
                                                                =
                                                                let uu____25753
                                                                  =
                                                                  let uu____25756
                                                                    =
                                                                    let uu____25757
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d  in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____25757
                                                                     in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____25756
                                                                   in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____25753)
                                                                 in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____25742
                                                               in
                                                            [uu____25741]  in
                                                          let uu____25762 =
                                                            let uu____25765 =
                                                              let uu____25768
                                                                =
                                                                let uu____25771
                                                                  =
                                                                  let uu____25774
                                                                    =
                                                                    let uu____25777
                                                                    =
                                                                    let uu____25780
                                                                    =
                                                                    let uu____25781
                                                                    =
                                                                    let uu____25788
                                                                    =
                                                                    let uu____25789
                                                                    =
                                                                    let uu____25800
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp)  in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____25800)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25789
                                                                     in
                                                                    (uu____25788,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25781
                                                                     in
                                                                    let uu____25813
                                                                    =
                                                                    let uu____25816
                                                                    =
                                                                    let uu____25817
                                                                    =
                                                                    let uu____25824
                                                                    =
                                                                    let uu____25825
                                                                    =
                                                                    let uu____25836
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars'  in
                                                                    let uu____25847
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred')
                                                                     in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____25836,
                                                                    uu____25847)
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____25825
                                                                     in
                                                                    (uu____25824,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok))
                                                                     in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____25817
                                                                     in
                                                                    [uu____25816]
                                                                     in
                                                                    uu____25780
                                                                    ::
                                                                    uu____25813
                                                                     in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____25777
                                                                     in
                                                                  FStar_List.append
                                                                    uu____25774
                                                                    elim
                                                                   in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____25771
                                                                 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____25768
                                                               in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____25765
                                                             in
                                                          FStar_List.append
                                                            uu____25738
                                                            uu____25762
                                                           in
                                                        FStar_List.append
                                                          decls3 uu____25735
                                                         in
                                                      FStar_List.append
                                                        decls2 uu____25732
                                                       in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____25729
                                                     in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))

and (encode_sigelts :
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____25893  ->
              fun se  ->
                match uu____25893 with
                | (g,env1) ->
                    let uu____25913 = encode_sigelt env1 se  in
                    (match uu____25913 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))

let (encode_env_bindings :
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____25970 =
        match uu____25970 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____26002 ->
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
                 ((let uu____26008 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding")
                      in
                   if uu____26008
                   then
                     let uu____26009 = FStar_Syntax_Print.bv_to_string x  in
                     let uu____26010 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort
                        in
                     let uu____26011 = FStar_Syntax_Print.term_to_string t1
                        in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____26009 uu____26010 uu____26011
                   else ());
                  (let uu____26013 = encode_term t1 env1  in
                   match uu____26013 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t  in
                       let uu____26029 =
                         let uu____26036 =
                           let uu____26037 =
                             let uu____26038 =
                               FStar_Util.digest_of_string t_hash  in
                             Prims.strcat uu____26038
                               (Prims.strcat "_" (Prims.string_of_int i))
                              in
                           Prims.strcat "x_" uu____26037  in
                         new_term_constant_from_string env1 x uu____26036  in
                       (match uu____26029 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t
                               in
                            let caption =
                              let uu____26054 = FStar_Options.log_queries ()
                                 in
                              if uu____26054
                              then
                                let uu____26057 =
                                  let uu____26058 =
                                    FStar_Syntax_Print.bv_to_string x  in
                                  let uu____26059 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort
                                     in
                                  let uu____26060 =
                                    FStar_Syntax_Print.term_to_string t1  in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____26058 uu____26059 uu____26060
                                   in
                                FStar_Pervasives_Native.Some uu____26057
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____26076,t)) ->
                 let t_norm = whnf env1 t  in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None
                    in
                 let uu____26090 = encode_free_var false env1 fv t t_norm []
                    in
                 (match uu____26090 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____26113,se,uu____26115) ->
                 let uu____26120 = encode_sigelt env1 se  in
                 (match uu____26120 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____26137,se) ->
                 let uu____26143 = encode_sigelt env1 se  in
                 (match uu____26143 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env')))
         in
      let uu____26160 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env)
         in
      match uu____26160 with | (uu____26183,decls,env1) -> (decls, env1)
  
let encode_labels :
  'Auu____26195 'Auu____26196 .
    ((Prims.string,FStar_SMTEncoding_Term.sort)
       FStar_Pervasives_Native.tuple2,'Auu____26196,'Auu____26195)
      FStar_Pervasives_Native.tuple3 Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_Term.decl
                                                Prims.list)
        FStar_Pervasives_Native.tuple2
  =
  fun labs  ->
    let prefix1 =
      FStar_All.pipe_right labs
        (FStar_List.map
           (fun uu____26264  ->
              match uu____26264 with
              | (l,uu____26276,uu____26277) ->
                  FStar_SMTEncoding_Term.DeclFun
                    ((FStar_Pervasives_Native.fst l), [],
                      FStar_SMTEncoding_Term.Bool_sort,
                      FStar_Pervasives_Native.None)))
       in
    let suffix =
      FStar_All.pipe_right labs
        (FStar_List.collect
           (fun uu____26323  ->
              match uu____26323 with
              | (l,uu____26337,uu____26338) ->
                  let uu____26347 =
                    FStar_All.pipe_left
                      (fun _0_45  -> FStar_SMTEncoding_Term.Echo _0_45)
                      (FStar_Pervasives_Native.fst l)
                     in
                  let uu____26348 =
                    let uu____26351 =
                      let uu____26352 = FStar_SMTEncoding_Util.mkFreeV l  in
                      FStar_SMTEncoding_Term.Eval uu____26352  in
                    [uu____26351]  in
                  uu____26347 :: uu____26348))
       in
    (prefix1, suffix)
  
let (last_env : env_t Prims.list FStar_ST.ref) = FStar_Util.mk_ref [] 
let (init_env : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    let uu____26377 =
      let uu____26380 =
        let uu____26381 = FStar_Util.smap_create (Prims.parse_int "100")  in
        let uu____26384 =
          let uu____26385 = FStar_TypeChecker_Env.current_module tcenv  in
          FStar_All.pipe_right uu____26385 FStar_Ident.string_of_lid  in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____26381;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____26384
        }  in
      [uu____26380]  in
    FStar_ST.op_Colon_Equals last_env uu____26377
  
let (get_env : FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t) =
  fun cmn  ->
    fun tcenv  ->
      let uu____26415 = FStar_ST.op_Bang last_env  in
      match uu____26415 with
      | [] -> failwith "No env; call init first!"
      | e::uu____26442 ->
          let uu___129_26445 = e  in
          let uu____26446 = FStar_Ident.string_of_lid cmn  in
          {
            bindings = (uu___129_26445.bindings);
            depth = (uu___129_26445.depth);
            tcenv;
            warn = (uu___129_26445.warn);
            cache = (uu___129_26445.cache);
            nolabels = (uu___129_26445.nolabels);
            use_zfuel_name = (uu___129_26445.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___129_26445.encode_non_total_function_typ);
            current_module_name = uu____26446
          }
  
let (set_env : env_t -> Prims.unit) =
  fun env  ->
    let uu____26450 = FStar_ST.op_Bang last_env  in
    match uu____26450 with
    | [] -> failwith "Empty env stack"
    | uu____26476::tl1 -> FStar_ST.op_Colon_Equals last_env (env :: tl1)
  
let (push_env : Prims.unit -> Prims.unit) =
  fun uu____26505  ->
    let uu____26506 = FStar_ST.op_Bang last_env  in
    match uu____26506 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache  in
        let top =
          let uu___130_26540 = hd1  in
          {
            bindings = (uu___130_26540.bindings);
            depth = (uu___130_26540.depth);
            tcenv = (uu___130_26540.tcenv);
            warn = (uu___130_26540.warn);
            cache = refs;
            nolabels = (uu___130_26540.nolabels);
            use_zfuel_name = (uu___130_26540.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___130_26540.encode_non_total_function_typ);
            current_module_name = (uu___130_26540.current_module_name)
          }  in
        FStar_ST.op_Colon_Equals last_env (top :: hd1 :: tl1)
  
let (pop_env : Prims.unit -> Prims.unit) =
  fun uu____26566  ->
    let uu____26567 = FStar_ST.op_Bang last_env  in
    match uu____26567 with
    | [] -> failwith "Popping an empty stack"
    | uu____26593::tl1 -> FStar_ST.op_Colon_Equals last_env tl1
  
let (init : FStar_TypeChecker_Env.env -> Prims.unit) =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
  
let (push : Prims.string -> Prims.unit) =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg 
let (pop : Prims.string -> Prims.unit) =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg 
let (open_fact_db_tags :
  env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list) = fun env  -> [] 
let (place_decl_in_fact_dbs :
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl)
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____26657::uu____26658,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___131_26666 = a  in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___131_26666.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___131_26666.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___131_26666.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____26667 -> d
  
let (fact_dbs_for_lid :
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list) =
  fun env  ->
    fun lid  ->
      let uu____26682 =
        let uu____26685 =
          let uu____26686 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns  in
          FStar_SMTEncoding_Term.Namespace uu____26686  in
        let uu____26687 = open_fact_db_tags env  in uu____26685 ::
          uu____26687
         in
      (FStar_SMTEncoding_Term.Name lid) :: uu____26682
  
let (encode_top_level_facts :
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env))
         in
      let uu____26709 = encode_sigelt env se  in
      match uu____26709 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids))
             in
          (g1, env1)
  
let (encode_sig :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit) =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____26745 = FStar_Options.log_queries ()  in
        if uu____26745
        then
          let uu____26748 =
            let uu____26749 =
              let uu____26750 =
                let uu____26751 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string)
                   in
                FStar_All.pipe_right uu____26751 (FStar_String.concat ", ")
                 in
              Prims.strcat "encoding sigelt " uu____26750  in
            FStar_SMTEncoding_Term.Caption uu____26749  in
          uu____26748 :: decls
        else decls  in
      (let uu____26762 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26762
       then
         let uu____26763 = FStar_Syntax_Print.sigelt_to_string se  in
         FStar_Util.print1 "+++++++++++Encoding sigelt %s\n" uu____26763
       else ());
      (let env =
         let uu____26766 = FStar_TypeChecker_Env.current_module tcenv  in
         get_env uu____26766 tcenv  in
       let uu____26767 = encode_top_level_facts env se  in
       match uu____26767 with
       | (decls,env1) ->
           (set_env env1;
            (let uu____26781 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 uu____26781)))
  
let (encode_modul :
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit) =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str
         in
      (let uu____26793 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low
          in
       if uu____26793
       then
         let uu____26794 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int
            in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____26794
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv  in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____26829  ->
                 fun se  ->
                   match uu____26829 with
                   | (g,env2) ->
                       let uu____26849 = encode_top_level_facts env2 se  in
                       (match uu____26849 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1))
          in
       let uu____26872 =
         encode_signature
           (let uu___132_26881 = env  in
            {
              bindings = (uu___132_26881.bindings);
              depth = (uu___132_26881.depth);
              tcenv = (uu___132_26881.tcenv);
              warn = false;
              cache = (uu___132_26881.cache);
              nolabels = (uu___132_26881.nolabels);
              use_zfuel_name = (uu___132_26881.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___132_26881.encode_non_total_function_typ);
              current_module_name = (uu___132_26881.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports
          in
       match uu____26872 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____26898 = FStar_Options.log_queries ()  in
             if uu____26898
             then
               let msg = Prims.strcat "Externals for " name  in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1  in
           (set_env
              (let uu___133_26906 = env1  in
               {
                 bindings = (uu___133_26906.bindings);
                 depth = (uu___133_26906.depth);
                 tcenv = (uu___133_26906.tcenv);
                 warn = true;
                 cache = (uu___133_26906.cache);
                 nolabels = (uu___133_26906.nolabels);
                 use_zfuel_name = (uu___133_26906.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___133_26906.encode_non_total_function_typ);
                 current_module_name = (uu___133_26906.current_module_name)
               });
            (let uu____26908 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low  in
             if uu____26908
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls  in
             FStar_SMTEncoding_Z3.giveZ3 decls1)))
  
let (encode_query :
  (Prims.unit -> Prims.string) FStar_Pervasives_Native.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list,FStar_SMTEncoding_ErrorReporting.label
                                                  Prims.list,FStar_SMTEncoding_Term.decl,
          FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple4)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____26960 =
           let uu____26961 = FStar_TypeChecker_Env.current_module tcenv  in
           uu____26961.FStar_Ident.str  in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____26960);
        (let env =
           let uu____26963 = FStar_TypeChecker_Env.current_module tcenv  in
           get_env uu____26963 tcenv  in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) []
            in
         let uu____26975 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____27010 = aux rest  in
                 (match uu____27010 with
                  | (out,rest1) ->
                      let t =
                        let uu____27040 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort
                           in
                        match uu____27040 with
                        | FStar_Pervasives_Native.Some uu____27045 ->
                            let uu____27046 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_Syntax_Syntax.t_unit
                               in
                            FStar_Syntax_Util.refine uu____27046
                              x.FStar_Syntax_Syntax.sort
                        | uu____27047 -> x.FStar_Syntax_Syntax.sort  in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.Primops;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t
                         in
                      let uu____27051 =
                        let uu____27054 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___134_27057 = x  in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___134_27057.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___134_27057.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             })
                           in
                        uu____27054 :: out  in
                      (uu____27051, rest1))
             | uu____27062 -> ([], bindings1)  in
           let uu____27069 = aux bindings  in
           match uu____27069 with
           | (closing,bindings1) ->
               let uu____27094 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q
                  in
               (uu____27094, bindings1)
            in
         match uu____26975 with
         | (q1,bindings1) ->
             let uu____27117 =
               let uu____27122 =
                 FStar_List.filter
                   (fun uu___99_27127  ->
                      match uu___99_27127 with
                      | FStar_TypeChecker_Env.Binding_sig uu____27128 ->
                          false
                      | uu____27135 -> true) bindings1
                  in
               encode_env_bindings env uu____27122  in
             (match uu____27117 with
              | (env_decls,env1) ->
                  ((let uu____27153 =
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
                    if uu____27153
                    then
                      let uu____27154 = FStar_Syntax_Print.term_to_string q1
                         in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____27154
                    else ());
                   (let uu____27156 = encode_formula q1 env1  in
                    match uu____27156 with
                    | (phi,qdecls) ->
                        let uu____27177 =
                          let uu____27182 =
                            FStar_TypeChecker_Env.get_range tcenv  in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____27182 phi
                           in
                        (match uu____27177 with
                         | (labels,phi1) ->
                             let uu____27199 = encode_labels labels  in
                             (match uu____27199 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls)
                                     in
                                  let qry =
                                    let uu____27236 =
                                      let uu____27243 =
                                        FStar_SMTEncoding_Util.mkNot phi1  in
                                      let uu____27244 =
                                        varops.mk_unique "@query"  in
                                      (uu____27243,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____27244)
                                       in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____27236
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
  