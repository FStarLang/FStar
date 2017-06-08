open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___101_74  ->
       match uu___101_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
let subst_lcomp_opt s l =
  match l with
  | FStar_Pervasives_Native.Some (FStar_Util.Inl l1) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      FStar_Pervasives_Native.Some uu____114
  | uu____126 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___126_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___126_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___126_140.FStar_Syntax_Syntax.sort)
        } in
      let uu____142 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (a1.FStar_Syntax_Syntax.ppname).FStar_Ident.idText in
      FStar_All.pipe_left escape uu____142
let primitive_projector_by_pos:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident -> Prims.int -> Prims.string
  =
  fun env  ->
    fun lid  ->
      fun i  ->
        let fail uu____155 =
          let uu____156 =
            FStar_Util.format2
              "Projector %s on data constructor %s not found"
              (Prims.string_of_int i) lid.FStar_Ident.str in
          failwith uu____156 in
        let uu____157 = FStar_TypeChecker_Env.lookup_datacon env lid in
        match uu____157 with
        | (uu____160,t) ->
            let uu____162 =
              let uu____163 = FStar_Syntax_Subst.compress t in
              uu____163.FStar_Syntax_Syntax.n in
            (match uu____162 with
             | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
                 let uu____178 = FStar_Syntax_Subst.open_comp bs c in
                 (match uu____178 with
                  | (binders,uu____182) ->
                      if
                        (i < (Prims.parse_int "0")) ||
                          (i >= (FStar_List.length binders))
                      then fail ()
                      else
                        (let b = FStar_List.nth binders i in
                         mk_term_projector_name lid
                           (FStar_Pervasives_Native.fst b)))
             | uu____193 -> fail ())
let mk_term_projector_name_by_pos:
  FStar_Ident.lident -> Prims.int -> Prims.string =
  fun lid  ->
    fun i  ->
      let uu____200 =
        FStar_Util.format2 "%s_%s" lid.FStar_Ident.str
          (Prims.string_of_int i) in
      FStar_All.pipe_left escape uu____200
let mk_term_projector:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term
  =
  fun lid  ->
    fun a  ->
      let uu____207 =
        let uu____210 = mk_term_projector_name lid a in
        (uu____210,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____207
let mk_term_projector_by_pos:
  FStar_Ident.lident -> Prims.int -> FStar_SMTEncoding_Term.term =
  fun lid  ->
    fun i  ->
      let uu____217 =
        let uu____220 = mk_term_projector_name_by_pos lid i in
        (uu____220,
          (FStar_SMTEncoding_Term.Arrow
             (FStar_SMTEncoding_Term.Term_sort,
               FStar_SMTEncoding_Term.Term_sort))) in
      FStar_SMTEncoding_Util.mkFreeV uu____217
let mk_data_tester env l x =
  FStar_SMTEncoding_Term.mk_tester (escape l.FStar_Ident.str) x
type varops_t =
  {
  push: Prims.unit -> Prims.unit;
  pop: Prims.unit -> Prims.unit;
  mark: Prims.unit -> Prims.unit;
  reset_mark: Prims.unit -> Prims.unit;
  commit_mark: Prims.unit -> Prims.unit;
  new_var: FStar_Ident.ident -> Prims.int -> Prims.string;
  new_fvar: FStar_Ident.lident -> Prims.string;
  fresh: Prims.string -> Prims.string;
  string_const: Prims.string -> FStar_SMTEncoding_Term.term;
  next_id: Prims.unit -> Prims.int;
  mk_unique: Prims.string -> Prims.string;}
let varops: varops_t =
  let initial_ctr = Prims.parse_int "100" in
  let ctr = FStar_Util.mk_ref initial_ctr in
  let new_scope uu____410 =
    let uu____411 = FStar_Util.smap_create (Prims.parse_int "100") in
    let uu____413 = FStar_Util.smap_create (Prims.parse_int "100") in
    (uu____411, uu____413) in
  let scopes =
    let uu____424 = let uu____430 = new_scope () in [uu____430] in
    FStar_Util.mk_ref uu____424 in
  let mk_unique y =
    let y1 = escape y in
    let y2 =
      let uu____455 =
        let uu____457 = FStar_ST.read scopes in
        FStar_Util.find_map uu____457
          (fun uu____474  ->
             match uu____474 with
             | (names1,uu____481) -> FStar_Util.smap_try_find names1 y1) in
      match uu____455 with
      | FStar_Pervasives_Native.None  -> y1
      | FStar_Pervasives_Native.Some uu____486 ->
          (FStar_Util.incr ctr;
           (let uu____491 =
              let uu____492 =
                let uu____493 = FStar_ST.read ctr in
                Prims.string_of_int uu____493 in
              Prims.strcat "__" uu____492 in
            Prims.strcat y1 uu____491)) in
    let top_scope =
      let uu____498 =
        let uu____503 = FStar_ST.read scopes in FStar_List.hd uu____503 in
      FStar_All.pipe_left FStar_Pervasives_Native.fst uu____498 in
    FStar_Util.smap_add top_scope y2 true; y2 in
  let new_var pp rn =
    FStar_All.pipe_left mk_unique
      (Prims.strcat pp.FStar_Ident.idText
         (Prims.strcat "__" (Prims.string_of_int rn))) in
  let new_fvar lid = mk_unique lid.FStar_Ident.str in
  let next_id1 uu____542 = FStar_Util.incr ctr; FStar_ST.read ctr in
  let fresh1 pfx =
    let uu____553 =
      let uu____554 = next_id1 () in
      FStar_All.pipe_left Prims.string_of_int uu____554 in
    FStar_Util.format2 "%s_%s" pfx uu____553 in
  let string_const s =
    let uu____559 =
      let uu____561 = FStar_ST.read scopes in
      FStar_Util.find_map uu____561
        (fun uu____578  ->
           match uu____578 with
           | (uu____584,strings) -> FStar_Util.smap_try_find strings s) in
    match uu____559 with
    | FStar_Pervasives_Native.Some f -> f
    | FStar_Pervasives_Native.None  ->
        let id = next_id1 () in
        let f =
          let uu____593 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____593 in
        let top_scope =
          let uu____596 =
            let uu____601 = FStar_ST.read scopes in FStar_List.hd uu____601 in
          FStar_All.pipe_left FStar_Pervasives_Native.snd uu____596 in
        (FStar_Util.smap_add top_scope s f; f) in
  let push1 uu____629 =
    let uu____630 =
      let uu____636 = new_scope () in
      let uu____641 = FStar_ST.read scopes in uu____636 :: uu____641 in
    FStar_ST.write scopes uu____630 in
  let pop1 uu____668 =
    let uu____669 =
      let uu____675 = FStar_ST.read scopes in FStar_List.tl uu____675 in
    FStar_ST.write scopes uu____669 in
  let mark1 uu____702 = push1 () in
  let reset_mark1 uu____706 = pop1 () in
  let commit_mark1 uu____710 =
    let uu____711 = FStar_ST.read scopes in
    match uu____711 with
    | (hd1,hd2)::(next1,next2)::tl1 ->
        (FStar_Util.smap_fold hd1
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next1 key value)
           ();
         FStar_Util.smap_fold hd2
           (fun key  ->
              fun value  -> fun v1  -> FStar_Util.smap_add next2 key value)
           ();
         FStar_ST.write scopes ((next1, next2) :: tl1))
    | uu____771 -> failwith "Impossible" in
  {
    push = push1;
    pop = pop1;
    mark = mark1;
    reset_mark = reset_mark1;
    commit_mark = commit_mark1;
    new_var;
    new_fvar;
    fresh = fresh1;
    string_const;
    next_id = next_id1;
    mk_unique
  }
let unmangle: FStar_Syntax_Syntax.bv -> FStar_Syntax_Syntax.bv =
  fun x  ->
    let uu___127_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___127_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_780.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
  FStar_Pervasives_Native.tuple2
  | Binding_fvar of
  (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                     FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                                    FStar_Pervasives_Native.option)
  FStar_Pervasives_Native.tuple4
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____802 -> false
let __proj__Binding_var__item___0:
  binding ->
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
      FStar_Pervasives_Native.tuple2
  = fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____826 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident,Prims.string,FStar_SMTEncoding_Term.term
                                       FStar_Pervasives_Native.option,
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option)
      FStar_Pervasives_Native.tuple4
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, FStar_Pervasives_Native.None)
type cache_entry =
  {
  cache_symbol_name: Prims.string;
  cache_symbol_arg_sorts: FStar_SMTEncoding_Term.sort Prims.list;
  cache_symbol_decls: FStar_SMTEncoding_Term.decl Prims.list;
  cache_symbol_assumption_names: Prims.string Prims.list;}
type env_t =
  {
  bindings: binding Prims.list;
  depth: Prims.int;
  tcenv: FStar_TypeChecker_Env.env;
  warn: Prims.bool;
  cache: cache_entry FStar_Util.smap;
  nolabels: Prims.bool;
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___102_1001  ->
            match uu___102_1001 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1004 -> [])) in
  {
    cache_symbol_name = tsym;
    cache_symbol_arg_sorts = cvar_sorts;
    cache_symbol_decls = t_decls;
    cache_symbol_assumption_names = names1
  }
let use_cache_entry: cache_entry -> FStar_SMTEncoding_Term.decl Prims.list =
  fun ce  ->
    [FStar_SMTEncoding_Term.RetainAssumptions
       (ce.cache_symbol_assumption_names)]
let print_env: env_t -> Prims.string =
  fun e  ->
    let uu____1012 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___103_1016  ->
              match uu___103_1016 with
              | Binding_var (x,uu____1018) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1020,uu____1021,uu____1022) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1012 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t:
  env_t ->
    FStar_Syntax_Syntax.term -> Prims.string FStar_Pervasives_Native.option
  =
  fun env  ->
    fun t  ->
      let uu____1055 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1055
      then
        let uu____1057 = FStar_Syntax_Print.term_to_string t in
        FStar_Pervasives_Native.Some uu____1057
      else FStar_Pervasives_Native.None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1068 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1068)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___128_1080 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___128_1080.tcenv);
           warn = (uu___128_1080.warn);
           cache = (uu___128_1080.cache);
           nolabels = (uu___128_1080.nolabels);
           use_zfuel_name = (uu___128_1080.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___128_1080.encode_non_total_function_typ);
           current_module_name = (uu___128_1080.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string,FStar_SMTEncoding_Term.term,env_t)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___129_1093 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___129_1093.depth);
           tcenv = (uu___129_1093.tcenv);
           warn = (uu___129_1093.warn);
           cache = (uu___129_1093.cache);
           nolabels = (uu___129_1093.nolabels);
           use_zfuel_name = (uu___129_1093.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1093.encode_non_total_function_typ);
           current_module_name = (uu___129_1093.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string ->
        (Prims.string,FStar_SMTEncoding_Term.term,env_t)
          FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___130_1109 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___130_1109.depth);
             tcenv = (uu___130_1109.tcenv);
             warn = (uu___130_1109.warn);
             cache = (uu___130_1109.cache);
             nolabels = (uu___130_1109.nolabels);
             use_zfuel_name = (uu___130_1109.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___130_1109.encode_non_total_function_typ);
             current_module_name = (uu___130_1109.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___131_1119 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___131_1119.depth);
          tcenv = (uu___131_1119.tcenv);
          warn = (uu___131_1119.warn);
          cache = (uu___131_1119.cache);
          nolabels = (uu___131_1119.nolabels);
          use_zfuel_name = (uu___131_1119.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___131_1119.encode_non_total_function_typ);
          current_module_name = (uu___131_1119.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___104_1135  ->
             match uu___104_1135 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 FStar_Pervasives_Native.Some (b, t)
             | uu____1143 -> FStar_Pervasives_Native.None) in
      let uu____1146 = aux a in
      match uu____1146 with
      | FStar_Pervasives_Native.None  ->
          let a2 = unmangle a in
          let uu____1153 = aux a2 in
          (match uu____1153 with
           | FStar_Pervasives_Native.None  ->
               let uu____1159 =
                 let uu____1160 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1161 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1160 uu____1161 in
               failwith uu____1159
           | FStar_Pervasives_Native.Some (b,t) -> t)
      | FStar_Pervasives_Native.Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,Prims.string,env_t) FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1181 =
        let uu___132_1182 = env in
        let uu____1183 =
          let uu____1185 =
            let uu____1186 =
              let uu____1193 =
                let uu____1195 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left
                  (fun _0_29  -> FStar_Pervasives_Native.Some _0_29)
                  uu____1195 in
              (x, fname, uu____1193, FStar_Pervasives_Native.None) in
            Binding_fvar uu____1186 in
          uu____1185 :: (env.bindings) in
        {
          bindings = uu____1183;
          depth = (uu___132_1182.depth);
          tcenv = (uu___132_1182.tcenv);
          warn = (uu___132_1182.warn);
          cache = (uu___132_1182.cache);
          nolabels = (uu___132_1182.nolabels);
          use_zfuel_name = (uu___132_1182.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1182.encode_non_total_function_typ);
          current_module_name = (uu___132_1182.current_module_name)
        } in
      (fname, ftok, uu____1181)
let try_lookup_lid:
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
        (fun uu___105_1217  ->
           match uu___105_1217 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               FStar_Pervasives_Native.Some (t1, t2, t3)
           | uu____1239 -> FStar_Pervasives_Native.None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1251 =
        lookup_binding env
          (fun uu___106_1253  ->
             match uu___106_1253 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 FStar_Pervasives_Native.Some ()
             | uu____1263 -> FStar_Pervasives_Native.None) in
      FStar_All.pipe_right uu____1251 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string,FStar_SMTEncoding_Term.term
                      FStar_Pervasives_Native.option,FStar_SMTEncoding_Term.term
                                                       FStar_Pervasives_Native.option)
        FStar_Pervasives_Native.tuple3
  =
  fun env  ->
    fun a  ->
      let uu____1276 = try_lookup_lid env a in
      match uu____1276 with
      | FStar_Pervasives_Native.None  ->
          let uu____1293 =
            let uu____1294 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1294 in
          failwith uu____1293
      | FStar_Pervasives_Native.Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___133_1325 = env in
          {
            bindings =
              ((Binding_fvar (x, fname, ftok, FStar_Pervasives_Native.None))
              :: (env.bindings));
            depth = (uu___133_1325.depth);
            tcenv = (uu___133_1325.tcenv);
            warn = (uu___133_1325.warn);
            cache = (uu___133_1325.cache);
            nolabels = (uu___133_1325.nolabels);
            use_zfuel_name = (uu___133_1325.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___133_1325.encode_non_total_function_typ);
            current_module_name = (uu___133_1325.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1337 = lookup_lid env x in
        match uu____1337 with
        | (t1,t2,uu____1345) ->
            let t3 =
              let uu____1351 =
                let uu____1355 =
                  let uu____1357 = FStar_SMTEncoding_Util.mkApp ("ZFuel", []) in
                  [uu____1357] in
                (f, uu____1355) in
              FStar_SMTEncoding_Util.mkApp uu____1351 in
            let uu___134_1360 = env in
            {
              bindings =
                ((Binding_fvar (x, t1, t2, (FStar_Pervasives_Native.Some t3)))
                :: (env.bindings));
              depth = (uu___134_1360.depth);
              tcenv = (uu___134_1360.tcenv);
              warn = (uu___134_1360.warn);
              cache = (uu___134_1360.cache);
              nolabels = (uu___134_1360.nolabels);
              use_zfuel_name = (uu___134_1360.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___134_1360.encode_non_total_function_typ);
              current_module_name = (uu___134_1360.current_module_name)
            }
let try_lookup_free_var:
  env_t ->
    FStar_Ident.lident ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun l  ->
      let uu____1370 = try_lookup_lid env l in
      match uu____1370 with
      | FStar_Pervasives_Native.None  -> FStar_Pervasives_Native.None
      | FStar_Pervasives_Native.Some (name,sym,zf_opt) ->
          (match zf_opt with
           | FStar_Pervasives_Native.Some f when env.use_zfuel_name ->
               FStar_Pervasives_Native.Some f
           | uu____1397 ->
               (match sym with
                | FStar_Pervasives_Native.Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1402,fuel::[]) ->
                         let uu____1405 =
                           let uu____1406 =
                             let uu____1407 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1407
                               FStar_Pervasives_Native.fst in
                           FStar_Util.starts_with uu____1406 "fuel" in
                         if uu____1405
                         then
                           let uu____1409 =
                             let uu____1410 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1410
                               fuel in
                           FStar_All.pipe_left
                             (fun _0_30  ->
                                FStar_Pervasives_Native.Some _0_30)
                             uu____1409
                         else FStar_Pervasives_Native.Some t
                     | uu____1413 -> FStar_Pervasives_Native.Some t)
                | uu____1414 -> FStar_Pervasives_Native.None))
let lookup_free_var env a =
  let uu____1432 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1432 with
  | FStar_Pervasives_Native.Some t -> t
  | FStar_Pervasives_Native.None  ->
      let uu____1435 =
        let uu____1436 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1436 in
      failwith uu____1435
let lookup_free_var_name env a =
  let uu____1453 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1453 with | (x,uu____1460,uu____1461) -> x
let lookup_free_var_sym env a =
  let uu____1485 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1485 with
  | (name,sym,zf_opt) ->
      (match zf_opt with
       | FStar_Pervasives_Native.Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1506;
             FStar_SMTEncoding_Term.rng = uu____1507;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1515 ->
           (match sym with
            | FStar_Pervasives_Native.None  ->
                ((FStar_SMTEncoding_Term.Var name), [])
            | FStar_Pervasives_Native.Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1529 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t ->
    Prims.string ->
      FStar_SMTEncoding_Term.term FStar_Pervasives_Native.option
  =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___107_1538  ->
           match uu___107_1538 with
           | Binding_fvar (uu____1540,nm',tok,uu____1543) when nm = nm' ->
               tok
           | uu____1548 -> FStar_Pervasives_Native.None)
let mkForall_fuel' n1 uu____1565 =
  match uu____1565 with
  | (pats,vars,body) ->
      let fallback uu____1581 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1584 = FStar_Options.unthrottle_inductives () in
      if uu____1584
      then fallback ()
      else
        (let uu____1586 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1586 with
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
                       | uu____1605 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1619 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1619
                     | uu____1621 ->
                         let uu____1622 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1622 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1625 -> body in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list,FStar_SMTEncoding_Term.fvs,
    FStar_SMTEncoding_Term.term) FStar_Pervasives_Native.tuple3 ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow uu____1651 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1659 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1664 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1665 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1674 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1689 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1691 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1691 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1705;
             FStar_Syntax_Syntax.pos = uu____1706;
             FStar_Syntax_Syntax.vars = uu____1707;_},uu____1708)
          ->
          let uu____1723 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1723 FStar_Option.isNone
      | uu____1736 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1743 =
        let uu____1744 = FStar_Syntax_Util.un_uinst t in
        uu____1744.FStar_Syntax_Syntax.n in
      match uu____1743 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1747,uu____1748,FStar_Pervasives_Native.Some (FStar_Util.Inr
           (l,flags)))
          ->
          ((FStar_Ident.lid_equals l FStar_Parser_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Parser_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1777  ->
                  match uu___108_1777 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1778 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1779,uu____1780,FStar_Pervasives_Native.Some (FStar_Util.Inl
           lc))
          -> FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1807 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1807 FStar_Option.isSome
      | uu____1820 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1827 = head_normal env t in
      if uu____1827
      then t
      else
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.WHNF;
          FStar_TypeChecker_Normalize.Exclude
            FStar_TypeChecker_Normalize.Zeta;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let norm: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      FStar_TypeChecker_Normalize.normalize
        [FStar_TypeChecker_Normalize.Beta;
        FStar_TypeChecker_Normalize.Exclude FStar_TypeChecker_Normalize.Zeta;
        FStar_TypeChecker_Normalize.Eager_unfolding;
        FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t
let trivial_post: FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun t  ->
    let uu____1838 =
      let uu____1839 = FStar_Syntax_Syntax.null_binder t in [uu____1839] in
    let uu____1840 =
      FStar_Syntax_Syntax.fvar FStar_Parser_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant FStar_Pervasives_Native.None in
    FStar_Syntax_Util.abs uu____1838 uu____1840 FStar_Pervasives_Native.None
let mk_Apply:
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
                    let uu____1867 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1867
                | s ->
                    let uu____1870 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1870) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1882  ->
    match uu___109_1882 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1883 -> false
let is_an_eta_expansion:
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
                       FStar_SMTEncoding_Term.freevars = uu____1911;
                       FStar_SMTEncoding_Term.rng = uu____1912;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1926) ->
              let uu____1931 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1941 -> false) args (FStar_List.rev xs)) in
              if uu____1931
              then tok_of_name env f
              else FStar_Pervasives_Native.None
          | (uu____1944,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1947 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1949 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1949)) in
              if uu____1947
              then FStar_Pervasives_Native.Some t
              else FStar_Pervasives_Native.None
          | uu____1952 -> FStar_Pervasives_Native.None in
        check_partial_applications body (FStar_List.rev vars)
type label =
  (FStar_SMTEncoding_Term.fv,Prims.string,FStar_Range.range)
    FStar_Pervasives_Native.tuple3
type labels = label Prims.list
type pattern =
  {
  pat_vars:
    (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.fv)
      FStar_Pervasives_Native.tuple2 Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2;
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv,FStar_SMTEncoding_Term.term)
        FStar_Pervasives_Native.tuple2 Prims.list;}
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____2036 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2039  ->
    match uu___110_2039 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2041 =
          let uu____2045 =
            let uu____2047 =
              let uu____2048 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2048 in
            [uu____2047] in
          ("FStar.Char.Char", uu____2045) in
        FStar_SMTEncoding_Util.mkApp uu____2041
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.None ) ->
        let uu____2056 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2056
    | FStar_Const.Const_int (i,FStar_Pervasives_Native.Some uu____2058) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2067) ->
        let uu____2070 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2070
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2074 =
          let uu____2075 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2075 in
        failwith uu____2074
let as_function_typ:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t0  ->
      let rec aux norm1 t =
        let t1 = FStar_Syntax_Subst.compress t in
        match t1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_arrow uu____2094 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2102 ->
            let uu____2107 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2107
        | uu____2108 ->
            if norm1
            then let uu____2109 = whnf env t1 in aux false uu____2109
            else
              (let uu____2111 =
                 let uu____2112 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2113 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2112 uu____2113 in
               failwith uu____2111) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders,FStar_Syntax_Syntax.comp)
      FStar_Pervasives_Native.tuple2
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2134 ->
        let uu____2135 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2135)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2163::uu____2164::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Parser_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2167::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Parser_Const.op_Minus
  | uu____2169 -> false
let rec encode_binders:
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
        (let uu____2307 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2307
         then
           let uu____2308 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2308
         else ());
        (let uu____2310 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2346  ->
                   fun b  ->
                     match uu____2346 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2389 =
                           let x = unmangle (FStar_Pervasives_Native.fst b) in
                           let uu____2398 = gen_term_var env1 x in
                           match uu____2398 with
                           | (xxsym,xx,env') ->
                               let uu____2412 =
                                 let uu____2415 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2415 env1 xx in
                               (match uu____2412 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2389 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2310 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
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
          let uu____2503 = encode_term t env in
          match uu____2503 with
          | (t1,decls) ->
              let uu____2510 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2510, decls)
and encode_term_pred':
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
          let uu____2518 = encode_term t env in
          match uu____2518 with
          | (t1,decls) ->
              (match fuel_opt with
               | FStar_Pervasives_Native.None  ->
                   let uu____2527 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2527, decls)
               | FStar_Pervasives_Native.Some f ->
                   let uu____2529 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2529, decls))
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2535 = encode_args args_e env in
        match uu____2535 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2547 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2554 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2554 in
            let binary arg_tms1 =
              let uu____2563 =
                let uu____2564 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2564 in
              let uu____2565 =
                let uu____2566 =
                  let uu____2567 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2567 in
                FStar_SMTEncoding_Term.unboxInt uu____2566 in
              (uu____2563, uu____2565) in
            let mk_default uu____2572 =
              let uu____2573 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2573 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2618 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2618
              then
                let uu____2619 = let uu____2620 = mk_args ts in op uu____2620 in
                FStar_All.pipe_right uu____2619 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2643 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2643
              then
                let uu____2644 = binary ts in
                match uu____2644 with
                | (t1,t2) ->
                    let uu____2649 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2649
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2652 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2652
                 then
                   let uu____2653 = op (binary ts) in
                   FStar_All.pipe_right uu____2653
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Parser_Const.op_Addition, add1);
              (FStar_Parser_Const.op_Subtraction, sub1);
              (FStar_Parser_Const.op_Multiply, mul1);
              (FStar_Parser_Const.op_Division, div1);
              (FStar_Parser_Const.op_Modulus, modulus);
              (FStar_Parser_Const.op_Minus, minus)] in
            let uu____2743 =
              let uu____2749 =
                FStar_List.tryFind
                  (fun uu____2761  ->
                     match uu____2761 with
                     | (l,uu____2768) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2749 FStar_Util.must in
            (match uu____2743 with
             | (uu____2793,op) ->
                 let uu____2801 = op arg_tms in (uu____2801, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2808 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2808
       then
         let uu____2809 = FStar_Syntax_Print.tag_of_term t in
         let uu____2810 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2811 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2809 uu____2810
           uu____2811
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2815 ->
           let uu____2836 =
             let uu____2837 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2838 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2839 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2840 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2837
               uu____2838 uu____2839 uu____2840 in
           failwith uu____2836
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2843 =
             let uu____2844 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2845 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2846 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2847 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2844
               uu____2845 uu____2846 uu____2847 in
           failwith uu____2843
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2851 =
             let uu____2852 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2852 in
           failwith uu____2851
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2857) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2887) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2896 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2896, [])
       | FStar_Syntax_Syntax.Tm_type uu____2902 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2905) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2911 = encode_const c in (uu____2911, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2926 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2926 with
            | (binders1,res) ->
                let uu____2933 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2933
                then
                  let uu____2936 =
                    encode_binders FStar_Pervasives_Native.None binders1 env in
                  (match uu____2936 with
                   | (vars,guards,env',decls,uu____2951) ->
                       let fsym =
                         let uu____2961 = varops.fresh "f" in
                         (uu____2961, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2964 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2968 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2968.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2968.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2968.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2968.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2968.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2968.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2968.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2968.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2968.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2968.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2968.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2968.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2968.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2968.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2968.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2968.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2968.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2968.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2968.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2968.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2968.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2968.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2968.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2964 with
                        | (pre_opt,res_t) ->
                            let uu____2975 =
                              encode_term_pred FStar_Pervasives_Native.None
                                res_t env' app in
                            (match uu____2975 with
                             | (res_pred,decls') ->
                                 let uu____2982 =
                                   match pre_opt with
                                   | FStar_Pervasives_Native.None  ->
                                       let uu____2989 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2989, [])
                                   | FStar_Pervasives_Native.Some pre ->
                                       let uu____2992 =
                                         encode_formula pre env' in
                                       (match uu____2992 with
                                        | (guard,decls0) ->
                                            let uu____3000 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3000, decls0)) in
                                 (match uu____2982 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3008 =
                                          let uu____3014 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3014) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3008 in
                                      let cvars =
                                        let uu____3024 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3024
                                          (FStar_List.filter
                                             (fun uu____3030  ->
                                                match uu____3030 with
                                                | (x,uu____3034) ->
                                                    x <>
                                                      (FStar_Pervasives_Native.fst
                                                         fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3045 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3045 with
                                       | FStar_Pervasives_Native.Some
                                           cache_entry ->
                                           let uu____3050 =
                                             let uu____3051 =
                                               let uu____3055 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3055) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3051 in
                                           (uu____3050,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | FStar_Pervasives_Native.None  ->
                                           let tsym =
                                             let uu____3066 =
                                               let uu____3067 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3067 in
                                             varops.mk_unique uu____3066 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives_Native.snd
                                               cvars in
                                           let caption =
                                             let uu____3074 =
                                               FStar_Options.log_queries () in
                                             if uu____3074
                                             then
                                               let uu____3076 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____3076
                                             else
                                               FStar_Pervasives_Native.None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3082 =
                                               let uu____3086 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3086) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3082 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3094 =
                                               let uu____3098 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3098,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name), a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3094 in
                                           let f_has_t =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               f t1 in
                                           let f_has_t_z =
                                             FStar_SMTEncoding_Term.mk_HasTypeZ
                                               f t1 in
                                           let pre_typing =
                                             let a_name =
                                               Prims.strcat "pre_typing_"
                                                 tsym in
                                             let uu____3111 =
                                               let uu____3115 =
                                                 let uu____3116 =
                                                   let uu____3122 =
                                                     let uu____3123 =
                                                       let uu____3126 =
                                                         let uu____3127 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3127 in
                                                       (f_has_t, uu____3126) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3123 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3122) in
                                                 mkForall_fuel uu____3116 in
                                               (uu____3115,
                                                 (FStar_Pervasives_Native.Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3111 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3140 =
                                               let uu____3144 =
                                                 let uu____3145 =
                                                   let uu____3151 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3151) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3145 in
                                               (uu____3144,
                                                 (FStar_Pervasives_Native.Some
                                                    a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3140 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3165 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3165);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort,
                         FStar_Pervasives_Native.None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____3176 =
                       let uu____3180 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3180,
                         (FStar_Pervasives_Native.Some
                            "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3176 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3189 =
                       let uu____3193 =
                         let uu____3194 =
                           let uu____3200 =
                             let uu____3201 =
                               let uu____3204 =
                                 let uu____3205 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3205 in
                               (f_has_t, uu____3204) in
                             FStar_SMTEncoding_Util.mkImp uu____3201 in
                           ([[f_has_t]], [fsym], uu____3200) in
                         mkForall_fuel uu____3194 in
                       (uu____3193, (FStar_Pervasives_Native.Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3189 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3219 ->
           let uu____3224 =
             let uu____3227 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3227 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3232;
                 FStar_Syntax_Syntax.pos = uu____3233;
                 FStar_Syntax_Syntax.vars = uu____3234;_} ->
                 let uu____3241 =
                   FStar_Syntax_Subst.open_term
                     [(x, FStar_Pervasives_Native.None)] f in
                 (match uu____3241 with
                  | (b,f1) ->
                      let uu____3255 =
                        let uu____3256 = FStar_List.hd b in
                        FStar_Pervasives_Native.fst uu____3256 in
                      (uu____3255, f1))
             | uu____3261 -> failwith "impossible" in
           (match uu____3224 with
            | (x,f) ->
                let uu____3268 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3268 with
                 | (base_t,decls) ->
                     let uu____3275 = gen_term_var env x in
                     (match uu____3275 with
                      | (x1,xtm,env') ->
                          let uu____3284 = encode_formula f env' in
                          (match uu____3284 with
                           | (refinement,decls') ->
                               let uu____3291 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3291 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (FStar_Pervasives_Native.Some fterm)
                                        xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3302 =
                                        let uu____3304 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3308 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3304
                                          uu____3308 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3302 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3324  ->
                                              match uu____3324 with
                                              | (y,uu____3328) ->
                                                  (y <> x1) && (y <> fsym))) in
                                    let xfv =
                                      (x1, FStar_SMTEncoding_Term.Term_sort) in
                                    let ffv =
                                      (fsym,
                                        FStar_SMTEncoding_Term.Fuel_sort) in
                                    let tkey =
                                      FStar_SMTEncoding_Util.mkForall
                                        ([], (ffv :: xfv :: cvars1),
                                          encoding) in
                                    let tkey_hash =
                                      FStar_SMTEncoding_Term.hash_of_term
                                        tkey in
                                    let uu____3347 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3347 with
                                     | FStar_Pervasives_Native.Some
                                         cache_entry ->
                                         let uu____3352 =
                                           let uu____3353 =
                                             let uu____3357 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3357) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3353 in
                                         (uu____3352,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | FStar_Pervasives_Native.None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3369 =
                                             let uu____3370 =
                                               let uu____3371 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3371 in
                                             Prims.strcat module_name
                                               uu____3370 in
                                           varops.mk_unique uu____3369 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives_Native.snd
                                             cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               FStar_Pervasives_Native.None) in
                                         let t1 =
                                           let uu____3380 =
                                             let uu____3384 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3384) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3380 in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (FStar_Pervasives_Native.Some
                                                fterm) xtm t1 in
                                         let t_has_kind =
                                           FStar_SMTEncoding_Term.mk_HasType
                                             t1
                                             FStar_SMTEncoding_Term.mk_Term_type in
                                         let t_haseq_base =
                                           FStar_SMTEncoding_Term.mk_haseq
                                             base_t in
                                         let t_haseq_ref =
                                           FStar_SMTEncoding_Term.mk_haseq t1 in
                                         let t_haseq1 =
                                           let uu____3394 =
                                             let uu____3398 =
                                               let uu____3399 =
                                                 let uu____3405 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3405) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3399 in
                                             (uu____3398,
                                               (FStar_Pervasives_Native.Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3394 in
                                         let t_kinding =
                                           let uu____3415 =
                                             let uu____3419 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3419,
                                               (FStar_Pervasives_Native.Some
                                                  "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3415 in
                                         let t_interp =
                                           let uu____3429 =
                                             let uu____3433 =
                                               let uu____3434 =
                                                 let uu____3440 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3440) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3434 in
                                             let uu____3452 =
                                               let uu____3454 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               FStar_Pervasives_Native.Some
                                                 uu____3454 in
                                             (uu____3433, uu____3452,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3429 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3459 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3459);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3476 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3476 in
           let uu____3480 =
             encode_term_pred FStar_Pervasives_Native.None k env ttm in
           (match uu____3480 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3488 =
                    let uu____3492 =
                      let uu____3493 =
                        let uu____3494 =
                          let uu____3495 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3495 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3494 in
                      varops.mk_unique uu____3493 in
                    (t_has_k, (FStar_Pervasives_Native.Some "Uvar typing"),
                      uu____3492) in
                  FStar_SMTEncoding_Util.mkAssume uu____3488 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3501 ->
           let uu____3511 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3511 with
            | (head1,args_e) ->
                let uu____3539 =
                  let uu____3547 =
                    let uu____3548 = FStar_Syntax_Subst.compress head1 in
                    uu____3548.FStar_Syntax_Syntax.n in
                  (uu____3547, args_e) in
                (match uu____3539 with
                 | uu____3558 when head_redex env head1 ->
                     let uu____3566 = whnf env t in
                     encode_term uu____3566 env
                 | uu____3567 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = uu____3580;
                       FStar_Syntax_Syntax.pos = uu____3581;
                       FStar_Syntax_Syntax.vars = uu____3582;_},uu____3583),uu____3584::
                    (v1,uu____3586)::(v2,uu____3588)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____3626 = encode_term v1 env in
                     (match uu____3626 with
                      | (v11,decls1) ->
                          let uu____3633 = encode_term v2 env in
                          (match uu____3633 with
                           | (v21,decls2) ->
                               let uu____3640 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3640,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,uu____3643::(v1,uu____3645)::(v2,uu____3647)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Parser_Const.lexcons_lid
                     ->
                     let uu____3681 = encode_term v1 env in
                     (match uu____3681 with
                      | (v11,decls1) ->
                          let uu____3688 = encode_term v2 env in
                          (match uu____3688 with
                           | (v21,decls2) ->
                               let uu____3695 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3695,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3697) ->
                     let e0 =
                       let uu____3709 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3709 in
                     ((let uu____3715 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3715
                       then
                         let uu____3716 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3716
                       else ());
                      (let e =
                         let uu____3721 =
                           let uu____3722 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3723 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3722
                             uu____3723 in
                         uu____3721 FStar_Pervasives_Native.None
                           t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3732),(arg,uu____3734)::[]) -> encode_term arg env
                 | uu____3752 ->
                     let uu____3760 = encode_args args_e env in
                     (match uu____3760 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3793 = encode_term head1 env in
                            match uu____3793 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | FStar_Pervasives_Native.None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | FStar_Pervasives_Native.Some (formals,c)
                                     ->
                                     let uu____3832 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3832 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3874  ->
                                                 fun uu____3875  ->
                                                   match (uu____3874,
                                                           uu____3875)
                                                   with
                                                   | ((bv,uu____3889),
                                                      (a,uu____3891)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3905 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3905
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3910 =
                                            encode_term_pred
                                              FStar_Pervasives_Native.None ty
                                              env app_tm in
                                          (match uu____3910 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3920 =
                                                   let uu____3924 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3929 =
                                                     let uu____3930 =
                                                       let uu____3931 =
                                                         let uu____3932 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3932 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3931 in
                                                     varops.mk_unique
                                                       uu____3930 in
                                                   (uu____3924,
                                                     (FStar_Pervasives_Native.Some
                                                        "Partial app typing"),
                                                     uu____3929) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3920 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3949 = lookup_free_var_sym env fv in
                            match uu____3949 with
                            | (fname,fuel_args) ->
                                let tm =
                                  FStar_SMTEncoding_Util.mkApp'
                                    (fname,
                                      (FStar_List.append fuel_args args)) in
                                (tm, decls) in
                          let head2 = FStar_Syntax_Subst.compress head1 in
                          let head_type =
                            match head2.FStar_Syntax_Syntax.n with
                            | FStar_Syntax_Syntax.Tm_uinst
                                ({
                                   FStar_Syntax_Syntax.n =
                                     FStar_Syntax_Syntax.Tm_name x;
                                   FStar_Syntax_Syntax.tk = uu____3972;
                                   FStar_Syntax_Syntax.pos = uu____3973;
                                   FStar_Syntax_Syntax.vars = uu____3974;_},uu____3975)
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
                                   FStar_Syntax_Syntax.tk = uu____3986;
                                   FStar_Syntax_Syntax.pos = uu____3987;
                                   FStar_Syntax_Syntax.vars = uu____3988;_},uu____3989)
                                ->
                                let uu____3994 =
                                  let uu____3995 =
                                    let uu____3998 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3998
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____3995
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____3994
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4018 =
                                  let uu____4019 =
                                    let uu____4022 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4022
                                      FStar_Pervasives_Native.fst in
                                  FStar_All.pipe_right uu____4019
                                    FStar_Pervasives_Native.snd in
                                FStar_Pervasives_Native.Some uu____4018
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4041,(FStar_Util.Inl t1,uu____4043),uu____4044)
                                -> FStar_Pervasives_Native.Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4082,(FStar_Util.Inr c,uu____4084),uu____4085)
                                ->
                                FStar_Pervasives_Native.Some
                                  (FStar_Syntax_Util.comp_result c)
                            | uu____4123 -> FStar_Pervasives_Native.None in
                          (match head_type with
                           | FStar_Pervasives_Native.None  ->
                               encode_partial_app
                                 FStar_Pervasives_Native.None
                           | FStar_Pervasives_Native.Some head_type1 ->
                               let head_type2 =
                                 let uu____4143 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4143 in
                               let uu____4144 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4144 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                         ({
                                            FStar_Syntax_Syntax.n =
                                              FStar_Syntax_Syntax.Tm_fvar fv;
                                            FStar_Syntax_Syntax.tk =
                                              uu____4154;
                                            FStar_Syntax_Syntax.pos =
                                              uu____4155;
                                            FStar_Syntax_Syntax.vars =
                                              uu____4156;_},uu____4157)
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
                                     | uu____4181 ->
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
           let uu____4226 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4226 with
            | (bs1,body1,opening) ->
                let fallback uu____4241 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Imprecise function encoding")) in
                  let uu____4246 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4246, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4257 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4257
                  | FStar_Util.Inr (eff,uu____4259) ->
                      let uu____4265 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4265 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4310 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4311 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4311.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4311.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4311.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4311.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4311.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4311.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4311.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4311.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4311.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4311.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4311.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4311.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4311.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4311.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4311.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4311.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4311.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4311.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4311.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4311.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4311.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4311.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4311.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4310 FStar_Syntax_Syntax.U_unknown in
                        let uu____4312 =
                          let uu____4313 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4313 in
                        FStar_Util.Inl uu____4312
                    | FStar_Util.Inr (eff_name,uu____4320) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4351 =
                        let uu____4352 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4352 in
                      FStar_All.pipe_right uu____4351
                        (fun _0_31  -> FStar_Pervasives_Native.Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4364 =
                        let uu____4365 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4365
                          FStar_Pervasives_Native.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Parser_Const.effect_Tot_lid
                      then
                        let uu____4373 =
                          let uu____4374 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4374 in
                        FStar_All.pipe_right uu____4373
                          (fun _0_32  -> FStar_Pervasives_Native.Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Parser_Const.effect_GTot_lid
                        then
                          (let uu____4378 =
                             let uu____4379 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4379 in
                           FStar_All.pipe_right uu____4378
                             (fun _0_33  ->
                                FStar_Pervasives_Native.Some _0_33))
                        else FStar_Pervasives_Native.None in
                (match lopt with
                 | FStar_Pervasives_Native.None  ->
                     ((let uu____4390 =
                         let uu____4391 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4391 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4390);
                      fallback ())
                 | FStar_Pervasives_Native.Some lc ->
                     let lc1 = lc in
                     let uu____4406 =
                       (is_impure lc1) &&
                         (let uu____4407 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4407) in
                     if uu____4406
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4412 =
                          encode_binders FStar_Pervasives_Native.None bs1 env in
                        match uu____4412 with
                        | (vars,guards,envbody,decls,uu____4427) ->
                            let uu____4434 =
                              let uu____4442 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4442
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4434 with
                             | (lc2,body2) ->
                                 let uu____4467 = encode_term body2 envbody in
                                 (match uu____4467 with
                                  | (body3,decls') ->
                                      let uu____4474 =
                                        let uu____4479 = codomain_eff lc2 in
                                        match uu____4479 with
                                        | FStar_Pervasives_Native.None  ->
                                            (FStar_Pervasives_Native.None,
                                              [])
                                        | FStar_Pervasives_Native.Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4491 =
                                              encode_term tfun env in
                                            (match uu____4491 with
                                             | (t1,decls1) ->
                                                 ((FStar_Pervasives_Native.Some
                                                     t1), decls1)) in
                                      (match uu____4474 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4510 =
                                               let uu____4516 =
                                                 let uu____4517 =
                                                   let uu____4520 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4520, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4517 in
                                               ([], vars, uu____4516) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4510 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | FStar_Pervasives_Native.None 
                                                 -> cvars
                                             | FStar_Pervasives_Native.Some
                                                 t1 ->
                                                 let uu____4528 =
                                                   let uu____4530 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4530 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4528 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4541 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4541 with
                                            | FStar_Pervasives_Native.Some
                                                cache_entry ->
                                                let uu____4546 =
                                                  let uu____4547 =
                                                    let uu____4551 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4551) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4547 in
                                                (uu____4546,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | FStar_Pervasives_Native.None 
                                                ->
                                                let uu____4557 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4557 with
                                                 | FStar_Pervasives_Native.Some
                                                     t1 ->
                                                     let decls1 =
                                                       let uu____4564 =
                                                         let uu____4565 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4565 =
                                                           cache_size in
                                                       if uu____4564
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'') in
                                                     (t1, decls1)
                                                 | FStar_Pervasives_Native.None
                                                      ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives_Native.snd
                                                         cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4576 =
                                                           let uu____4577 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4577 in
                                                         varops.mk_unique
                                                           uu____4576 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           FStar_Pervasives_Native.None) in
                                                     let f =
                                                       let uu____4582 =
                                                         let uu____4586 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4586) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4582 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | FStar_Pervasives_Native.None
                                                            -> []
                                                       | FStar_Pervasives_Native.Some
                                                           t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               FStar_Pervasives_Native.None
                                                               f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4598 =
                                                             let uu____4599 =
                                                               let uu____4603
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4603,
                                                                 (FStar_Pervasives_Native.Some
                                                                    a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4599 in
                                                           [uu____4598] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4611 =
                                                         let uu____4615 =
                                                           let uu____4616 =
                                                             let uu____4622 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4622) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4616 in
                                                         (uu____4615,
                                                           (FStar_Pervasives_Native.Some
                                                              a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4611 in
                                                     let f_decls =
                                                       FStar_List.append
                                                         decls
                                                         (FStar_List.append
                                                            decls'
                                                            (FStar_List.append
                                                               decls''
                                                               (FStar_List.append
                                                                  (fdecl ::
                                                                  typing_f)
                                                                  [interp_f]))) in
                                                     ((let uu____4632 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4632);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4634,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4635;
                          FStar_Syntax_Syntax.lbunivs = uu____4636;
                          FStar_Syntax_Syntax.lbtyp = uu____4637;
                          FStar_Syntax_Syntax.lbeff = uu____4638;
                          FStar_Syntax_Syntax.lbdef = uu____4639;_}::uu____4640),uu____4641)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4659;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4661;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4677 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort,
                   FStar_Pervasives_Native.None) in
             let uu____4690 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4690, [decl_e])))
       | FStar_Syntax_Syntax.Tm_match (e,pats) ->
           encode_match e pats FStar_SMTEncoding_Term.mk_Term_unit env
             encode_term)
and encode_let:
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
              let uu____4732 = encode_term e1 env in
              match uu____4732 with
              | (ee1,decls1) ->
                  let uu____4739 =
                    FStar_Syntax_Subst.open_term
                      [(x, FStar_Pervasives_Native.None)] e2 in
                  (match uu____4739 with
                   | (xs,e21) ->
                       let uu____4753 = FStar_List.hd xs in
                       (match uu____4753 with
                        | (x1,uu____4761) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4763 = encode_body e21 env' in
                            (match uu____4763 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
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
            let uu____4785 =
              let uu____4789 =
                let uu____4790 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown
                    FStar_Pervasives_Native.None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4790 in
              gen_term_var env uu____4789 in
            match uu____4785 with
            | (scrsym,scr',env1) ->
                let uu____4800 = encode_term e env1 in
                (match uu____4800 with
                 | (scr,decls) ->
                     let uu____4807 =
                       let encode_branch b uu____4823 =
                         match uu____4823 with
                         | (else_case,decls1) ->
                             let uu____4834 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4834 with
                              | (p,w,br) ->
                                  let uu____4855 = encode_pat env1 p in
                                  (match uu____4855 with
                                   | (env0,pattern) ->
                                       let guard = pattern.guard scr' in
                                       let projections =
                                         pattern.projections scr' in
                                       let env2 =
                                         FStar_All.pipe_right projections
                                           (FStar_List.fold_left
                                              (fun env2  ->
                                                 fun uu____4875  ->
                                                   match uu____4875 with
                                                   | (x,t) ->
                                                       push_term_var env2 x t)
                                              env1) in
                                       let uu____4880 =
                                         match w with
                                         | FStar_Pervasives_Native.None  ->
                                             (guard, [])
                                         | FStar_Pervasives_Native.Some w1 ->
                                             let uu____4895 =
                                               encode_term w1 env2 in
                                             (match uu____4895 with
                                              | (w2,decls2) ->
                                                  let uu____4903 =
                                                    let uu____4904 =
                                                      let uu____4907 =
                                                        let uu____4908 =
                                                          let uu____4911 =
                                                            FStar_SMTEncoding_Term.boxBool
                                                              FStar_SMTEncoding_Util.mkTrue in
                                                          (w2, uu____4911) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____4908 in
                                                      (guard, uu____4907) in
                                                    FStar_SMTEncoding_Util.mkAnd
                                                      uu____4904 in
                                                  (uu____4903, decls2)) in
                                       (match uu____4880 with
                                        | (guard1,decls2) ->
                                            let uu____4919 =
                                              encode_br br env2 in
                                            (match uu____4919 with
                                             | (br1,decls3) ->
                                                 let uu____4927 =
                                                   FStar_SMTEncoding_Util.mkITE
                                                     (guard1, br1, else_case) in
                                                 (uu____4927,
                                                   (FStar_List.append decls1
                                                      (FStar_List.append
                                                         decls2 decls3))))))) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4807 with
                      | (match_tm,decls1) ->
                          let uu____4938 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4938, decls1)))
and encode_pat:
  env_t ->
    FStar_Syntax_Syntax.pat -> (env_t,pattern) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun pat  ->
      (let uu____4960 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4960
       then
         let uu____4961 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4961
       else ());
      (let uu____4963 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4963 with
       | (vars,pat_term) ->
           let uu____4973 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4996  ->
                     fun v1  ->
                       match uu____4996 with
                       | (env1,vars1) ->
                           let uu____5024 = gen_term_var env1 v1 in
                           (match uu____5024 with
                            | (xx,uu____5036,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4973 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_var uu____5083 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_wild uu____5084 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_dot_term uu____5085 ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____5091 =
                        let uu____5094 = encode_const c in
                        (scrutinee, uu____5094) in
                      FStar_SMTEncoding_Util.mkEq uu____5091
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5113 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5113 with
                        | (uu____5117,uu____5118::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5120 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5141  ->
                                  match uu____5141 with
                                  | (arg,uu____5147) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5157 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5157)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_dot_term (x,uu____5177) ->
                      [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_var x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5196 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5211 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5233  ->
                                  match uu____5233 with
                                  | (arg,uu____5242) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5252 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5252)) in
                      FStar_All.pipe_right uu____5211 FStar_List.flatten in
                let pat_term1 uu____5268 = encode_term pat_term env1 in
                let pattern =
                  {
                    pat_vars = vars1;
                    pat_term = pat_term1;
                    guard = (mk_guard pat);
                    projections = (mk_projections pat)
                  } in
                (env1, pattern)))
and encode_args:
  FStar_Syntax_Syntax.args ->
    env_t ->
      (FStar_SMTEncoding_Term.term Prims.list,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun l  ->
    fun env  ->
      let uu____5275 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5290  ->
                fun uu____5291  ->
                  match (uu____5290, uu____5291) with
                  | ((tms,decls),(t,uu____5311)) ->
                      let uu____5322 = encode_term t env in
                      (match uu____5322 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5275 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5356 = FStar_Syntax_Util.list_elements e in
        match uu____5356 with
        | FStar_Pervasives_Native.Some l -> l
        | FStar_Pervasives_Native.None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5371 =
          let uu____5381 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5381 FStar_Syntax_Util.head_and_args in
        match uu____5371 with
        | (head1,args) ->
            let uu____5409 =
              let uu____5417 =
                let uu____5418 = FStar_Syntax_Util.un_uinst head1 in
                uu____5418.FStar_Syntax_Syntax.n in
              (uu____5417, args) in
            (match uu____5409 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5429,uu____5430)::(e,uu____5432)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpat_lid
                 -> e
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5460)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.smtpatT_lid
                 -> e
             | uu____5478 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5505 =
            let uu____5515 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5515 FStar_Syntax_Util.head_and_args in
          match uu____5505 with
          | (head1,args) ->
              let uu____5544 =
                let uu____5552 =
                  let uu____5553 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5553.FStar_Syntax_Syntax.n in
                (uu____5552, args) in
              (match uu____5544 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5566)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Parser_Const.smtpatOr_lid
                   -> FStar_Pervasives_Native.Some e
               | uu____5586 -> FStar_Pervasives_Native.None) in
        match elts with
        | t1::[] ->
            let uu____5601 = smt_pat_or t1 in
            (match uu____5601 with
             | FStar_Pervasives_Native.Some e ->
                 let uu____5614 = list_elements1 e in
                 FStar_All.pipe_right uu____5614
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5625 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5625
                           (FStar_List.map one_pat)))
             | uu____5633 ->
                 let uu____5637 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5637])
        | uu____5653 ->
            let uu____5655 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5655] in
      let uu____5671 =
        let uu____5684 =
          let uu____5685 = FStar_Syntax_Subst.compress t in
          uu____5685.FStar_Syntax_Syntax.n in
        match uu____5684 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5712 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5712 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5741;
                        FStar_Syntax_Syntax.effect_name = uu____5742;
                        FStar_Syntax_Syntax.result_typ = uu____5743;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5745)::(post,uu____5747)::(pats,uu____5749)::[];
                        FStar_Syntax_Syntax.flags = uu____5750;_}
                      ->
                      let uu____5782 = lemma_pats pats in
                      (binders1, pre, post, uu____5782)
                  | uu____5795 -> failwith "impos"))
        | uu____5808 -> failwith "Impos" in
      match uu____5671 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5844 = env in
            {
              bindings = (uu___137_5844.bindings);
              depth = (uu___137_5844.depth);
              tcenv = (uu___137_5844.tcenv);
              warn = (uu___137_5844.warn);
              cache = (uu___137_5844.cache);
              nolabels = (uu___137_5844.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5844.encode_non_total_function_typ);
              current_module_name = (uu___137_5844.current_module_name)
            } in
          let uu____5845 =
            encode_binders FStar_Pervasives_Native.None binders env1 in
          (match uu____5845 with
           | (vars,guards,env2,decls,uu____5860) ->
               let uu____5867 =
                 let uu____5874 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5896 =
                             let uu____5901 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5901 FStar_List.unzip in
                           match uu____5896 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5874 FStar_List.unzip in
               (match uu____5867 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_5959 = env2 in
                      {
                        bindings = (uu___138_5959.bindings);
                        depth = (uu___138_5959.depth);
                        tcenv = (uu___138_5959.tcenv);
                        warn = (uu___138_5959.warn);
                        cache = (uu___138_5959.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_5959.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_5959.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_5959.current_module_name)
                      } in
                    let uu____5960 =
                      let uu____5963 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5963 env3 in
                    (match uu____5960 with
                     | (pre1,decls'') ->
                         let uu____5968 =
                           let uu____5971 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5971 env3 in
                         (match uu____5968 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____5978 =
                                let uu____5979 =
                                  let uu____5985 =
                                    let uu____5986 =
                                      let uu____5989 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____5989, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____5986 in
                                  (pats, vars, uu____5985) in
                                FStar_SMTEncoding_Util.mkForall uu____5979 in
                              (uu____5978, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t ->
      (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decls_t)
        FStar_Pervasives_Native.tuple2
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6002 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6002
        then
          let uu____6003 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6004 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6003 uu____6004
        else () in
      let enc f r l =
        let uu____6031 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6044 =
                   encode_term (FStar_Pervasives_Native.fst x) env in
                 match uu____6044 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6031 with
        | (decls,args) ->
            let uu____6061 =
              let uu___139_6062 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6062.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6062.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6061, decls) in
      let const_op f r uu____6081 = let uu____6084 = f r in (uu____6084, []) in
      let un_op f l =
        let uu____6100 = FStar_List.hd l in FStar_All.pipe_left f uu____6100 in
      let bin_op f uu___111_6113 =
        match uu___111_6113 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6121 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6148 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6157  ->
                 match uu____6157 with
                 | (t,uu____6165) ->
                     let uu____6166 = encode_formula t env in
                     (match uu____6166 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6148 with
        | (decls,phis) ->
            let uu____6183 =
              let uu___140_6184 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6184.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6184.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6183, decls) in
      let eq_op r uu___112_6200 =
        match uu___112_6200 with
        | uu____6203::e1::e2::[] ->
            let uu____6234 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6234 r [e1; e2]
        | uu____6253::uu____6254::e1::e2::[] ->
            let uu____6293 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6293 r [e1; e2]
        | l ->
            let uu____6313 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6313 r l in
      let mk_imp1 r uu___113_6332 =
        match uu___113_6332 with
        | (lhs,uu____6336)::(rhs,uu____6338)::[] ->
            let uu____6359 = encode_formula rhs env in
            (match uu____6359 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6368) ->
                      (l1, decls1)
                  | uu____6371 ->
                      let uu____6372 = encode_formula lhs env in
                      (match uu____6372 with
                       | (l2,decls2) ->
                           let uu____6379 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6379, (FStar_List.append decls1 decls2)))))
        | uu____6381 -> failwith "impossible" in
      let mk_ite r uu___114_6396 =
        match uu___114_6396 with
        | (guard,uu____6400)::(_then,uu____6402)::(_else,uu____6404)::[] ->
            let uu____6433 = encode_formula guard env in
            (match uu____6433 with
             | (g,decls1) ->
                 let uu____6440 = encode_formula _then env in
                 (match uu____6440 with
                  | (t,decls2) ->
                      let uu____6447 = encode_formula _else env in
                      (match uu____6447 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6456 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6475 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6475 in
      let connectives =
        let uu____6487 =
          let uu____6496 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Parser_Const.and_lid, uu____6496) in
        let uu____6509 =
          let uu____6519 =
            let uu____6528 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Parser_Const.or_lid, uu____6528) in
          let uu____6541 =
            let uu____6551 =
              let uu____6561 =
                let uu____6570 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Parser_Const.iff_lid, uu____6570) in
              let uu____6583 =
                let uu____6593 =
                  let uu____6603 =
                    let uu____6612 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Parser_Const.not_lid, uu____6612) in
                  [uu____6603;
                  (FStar_Parser_Const.eq2_lid, eq_op);
                  (FStar_Parser_Const.eq3_lid, eq_op);
                  (FStar_Parser_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Parser_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Parser_Const.ite_lid, mk_ite) :: uu____6593 in
              uu____6561 :: uu____6583 in
            (FStar_Parser_Const.imp_lid, mk_imp1) :: uu____6551 in
          uu____6519 :: uu____6541 in
        uu____6487 :: uu____6509 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6774 = encode_formula phi' env in
            (match uu____6774 with
             | (phi2,decls) ->
                 let uu____6781 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6781, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6782 ->
            let uu____6787 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6787 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6816 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6816 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6824;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6826;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6842 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6842 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6874::(x,uu____6876)::(t,uu____6878)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.has_type_lid
                 ->
                 let uu____6912 = encode_term x env in
                 (match uu____6912 with
                  | (x1,decls) ->
                      let uu____6919 = encode_term t env in
                      (match uu____6919 with
                       | (t1,decls') ->
                           let uu____6926 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6926, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6930)::(msg,uu____6932)::(phi2,uu____6934)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Parser_Const.labeled_lid
                 ->
                 let uu____6968 =
                   let uu____6971 =
                     let uu____6972 = FStar_Syntax_Subst.compress r in
                     uu____6972.FStar_Syntax_Syntax.n in
                   let uu____6975 =
                     let uu____6976 = FStar_Syntax_Subst.compress msg in
                     uu____6976.FStar_Syntax_Syntax.n in
                   (uu____6971, uu____6975) in
                 (match uu____6968 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6983))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) FStar_Pervasives_Native.None
                          r1 in
                      fallback phi3
                  | uu____6999 -> fallback phi2)
             | uu____7002 when head_redex env head2 ->
                 let uu____7010 = whnf env phi1 in
                 encode_formula uu____7010 env
             | uu____7011 ->
                 let uu____7019 = encode_term phi1 env in
                 (match uu____7019 with
                  | (tt,decls) ->
                      let uu____7026 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7027 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7027.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7027.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7026, decls)))
        | uu____7030 ->
            let uu____7031 = encode_term phi1 env in
            (match uu____7031 with
             | (tt,decls) ->
                 let uu____7038 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7039 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7039.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7039.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7038, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7066 = encode_binders FStar_Pervasives_Native.None bs env1 in
        match uu____7066 with
        | (vars,guards,env2,decls,uu____7088) ->
            let uu____7095 =
              let uu____7102 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7125 =
                          let uu____7130 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7144  ->
                                    match uu____7144 with
                                    | (t,uu____7150) ->
                                        encode_term t
                                          (let uu___143_7151 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7151.bindings);
                                             depth = (uu___143_7151.depth);
                                             tcenv = (uu___143_7151.tcenv);
                                             warn = (uu___143_7151.warn);
                                             cache = (uu___143_7151.cache);
                                             nolabels =
                                               (uu___143_7151.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7151.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7151.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7130 FStar_List.unzip in
                        match uu____7125 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7102 FStar_List.unzip in
            (match uu____7095 with
             | (pats,decls') ->
                 let uu____7203 = encode_formula body env2 in
                 (match uu____7203 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7222;
                             FStar_SMTEncoding_Term.rng = uu____7223;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Parser_Const.guard_free)
                              = gf
                            -> []
                        | uu____7231 -> guards in
                      let uu____7234 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7234, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7268  ->
                   match uu____7268 with
                   | (x,uu____7272) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7278 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7284 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7284) uu____7278 tl1 in
             let uu____7286 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7298  ->
                       match uu____7298 with
                       | (b,uu____7302) ->
                           let uu____7303 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7303)) in
             (match uu____7286 with
              | FStar_Pervasives_Native.None  -> ()
              | FStar_Pervasives_Native.Some (x,uu____7307) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7317 =
                    let uu____7318 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7318 in
                  FStar_Errors.warn pos uu____7317) in
       let uu____7319 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7319 with
       | FStar_Pervasives_Native.None  -> fallback phi1
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.BaseConn (op,arms))
           ->
           let uu____7325 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7361  ->
                     match uu____7361 with
                     | (l,uu____7371) -> FStar_Ident.lid_equals op l)) in
           (match uu____7325 with
            | FStar_Pervasives_Native.None  -> fallback phi1
            | FStar_Pervasives_Native.Some (uu____7394,f) ->
                f phi1.FStar_Syntax_Syntax.pos arms)
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QAll
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7423 = encode_q_body env vars pats body in
             match uu____7423 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7449 =
                     let uu____7455 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7455) in
                   FStar_SMTEncoding_Term.mkForall uu____7449
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | FStar_Pervasives_Native.Some (FStar_Syntax_Util.QEx
           (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7467 = encode_q_body env vars pats body in
             match uu____7467 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7492 =
                   let uu____7493 =
                     let uu____7499 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7499) in
                   FStar_SMTEncoding_Term.mkExists uu____7493
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7492, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term,FStar_SMTEncoding_Term.decl Prims.list)
          FStar_Pervasives_Native.tuple2;
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7548 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7548 with
  | (asym,a) ->
      let uu____7553 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7553 with
       | (xsym,x) ->
           let uu____7558 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7558 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7588 =
                      let uu____7594 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives_Native.snd) in
                      (x1, uu____7594, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7588 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                  let xapp =
                    let uu____7609 =
                      let uu____7613 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7613) in
                    FStar_SMTEncoding_Util.mkApp uu____7609 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7621 =
                    let uu____7623 =
                      let uu____7625 =
                        let uu____7627 =
                          let uu____7628 =
                            let uu____7632 =
                              let uu____7633 =
                                let uu____7639 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7639) in
                              FStar_SMTEncoding_Util.mkForall uu____7633 in
                            (uu____7632, FStar_Pervasives_Native.None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7628 in
                        let uu____7648 =
                          let uu____7650 =
                            let uu____7651 =
                              let uu____7655 =
                                let uu____7656 =
                                  let uu____7662 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7662) in
                                FStar_SMTEncoding_Util.mkForall uu____7656 in
                              (uu____7655,
                                (FStar_Pervasives_Native.Some
                                   "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7651 in
                          [uu____7650] in
                        uu____7627 :: uu____7648 in
                      xtok_decl :: uu____7625 in
                    xname_decl :: uu____7623 in
                  (xtok1, uu____7621) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7711 =
                    let uu____7719 =
                      let uu____7725 =
                        let uu____7726 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7726 in
                      quant axy uu____7725 in
                    (FStar_Parser_Const.op_Eq, uu____7719) in
                  let uu____7732 =
                    let uu____7741 =
                      let uu____7749 =
                        let uu____7755 =
                          let uu____7756 =
                            let uu____7757 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7757 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7756 in
                        quant axy uu____7755 in
                      (FStar_Parser_Const.op_notEq, uu____7749) in
                    let uu____7763 =
                      let uu____7772 =
                        let uu____7780 =
                          let uu____7786 =
                            let uu____7787 =
                              let uu____7788 =
                                let uu____7791 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7792 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7791, uu____7792) in
                              FStar_SMTEncoding_Util.mkLT uu____7788 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7787 in
                          quant xy uu____7786 in
                        (FStar_Parser_Const.op_LT, uu____7780) in
                      let uu____7798 =
                        let uu____7807 =
                          let uu____7815 =
                            let uu____7821 =
                              let uu____7822 =
                                let uu____7823 =
                                  let uu____7826 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7827 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7826, uu____7827) in
                                FStar_SMTEncoding_Util.mkLTE uu____7823 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7822 in
                            quant xy uu____7821 in
                          (FStar_Parser_Const.op_LTE, uu____7815) in
                        let uu____7833 =
                          let uu____7842 =
                            let uu____7850 =
                              let uu____7856 =
                                let uu____7857 =
                                  let uu____7858 =
                                    let uu____7861 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7862 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7861, uu____7862) in
                                  FStar_SMTEncoding_Util.mkGT uu____7858 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7857 in
                              quant xy uu____7856 in
                            (FStar_Parser_Const.op_GT, uu____7850) in
                          let uu____7868 =
                            let uu____7877 =
                              let uu____7885 =
                                let uu____7891 =
                                  let uu____7892 =
                                    let uu____7893 =
                                      let uu____7896 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7897 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7896, uu____7897) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7893 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7892 in
                                quant xy uu____7891 in
                              (FStar_Parser_Const.op_GTE, uu____7885) in
                            let uu____7903 =
                              let uu____7912 =
                                let uu____7920 =
                                  let uu____7926 =
                                    let uu____7927 =
                                      let uu____7928 =
                                        let uu____7931 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7932 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7931, uu____7932) in
                                      FStar_SMTEncoding_Util.mkSub uu____7928 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7927 in
                                  quant xy uu____7926 in
                                (FStar_Parser_Const.op_Subtraction,
                                  uu____7920) in
                              let uu____7938 =
                                let uu____7947 =
                                  let uu____7955 =
                                    let uu____7961 =
                                      let uu____7962 =
                                        let uu____7963 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7963 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7962 in
                                    quant qx uu____7961 in
                                  (FStar_Parser_Const.op_Minus, uu____7955) in
                                let uu____7969 =
                                  let uu____7978 =
                                    let uu____7986 =
                                      let uu____7992 =
                                        let uu____7993 =
                                          let uu____7994 =
                                            let uu____7997 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7998 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7997, uu____7998) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7994 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7993 in
                                      quant xy uu____7992 in
                                    (FStar_Parser_Const.op_Addition,
                                      uu____7986) in
                                  let uu____8004 =
                                    let uu____8013 =
                                      let uu____8021 =
                                        let uu____8027 =
                                          let uu____8028 =
                                            let uu____8029 =
                                              let uu____8032 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8033 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8032, uu____8033) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8029 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8028 in
                                        quant xy uu____8027 in
                                      (FStar_Parser_Const.op_Multiply,
                                        uu____8021) in
                                    let uu____8039 =
                                      let uu____8048 =
                                        let uu____8056 =
                                          let uu____8062 =
                                            let uu____8063 =
                                              let uu____8064 =
                                                let uu____8067 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8068 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8067, uu____8068) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8064 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8063 in
                                          quant xy uu____8062 in
                                        (FStar_Parser_Const.op_Division,
                                          uu____8056) in
                                      let uu____8074 =
                                        let uu____8083 =
                                          let uu____8091 =
                                            let uu____8097 =
                                              let uu____8098 =
                                                let uu____8099 =
                                                  let uu____8102 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8103 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8102, uu____8103) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8099 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8098 in
                                            quant xy uu____8097 in
                                          (FStar_Parser_Const.op_Modulus,
                                            uu____8091) in
                                        let uu____8109 =
                                          let uu____8118 =
                                            let uu____8126 =
                                              let uu____8132 =
                                                let uu____8133 =
                                                  let uu____8134 =
                                                    let uu____8137 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8138 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8137, uu____8138) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8134 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8133 in
                                              quant xy uu____8132 in
                                            (FStar_Parser_Const.op_And,
                                              uu____8126) in
                                          let uu____8144 =
                                            let uu____8153 =
                                              let uu____8161 =
                                                let uu____8167 =
                                                  let uu____8168 =
                                                    let uu____8169 =
                                                      let uu____8172 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8173 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8172,
                                                        uu____8173) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8169 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8168 in
                                                quant xy uu____8167 in
                                              (FStar_Parser_Const.op_Or,
                                                uu____8161) in
                                            let uu____8179 =
                                              let uu____8188 =
                                                let uu____8196 =
                                                  let uu____8202 =
                                                    let uu____8203 =
                                                      let uu____8204 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8204 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8203 in
                                                  quant qx uu____8202 in
                                                (FStar_Parser_Const.op_Negation,
                                                  uu____8196) in
                                              [uu____8188] in
                                            uu____8153 :: uu____8179 in
                                          uu____8118 :: uu____8144 in
                                        uu____8083 :: uu____8109 in
                                      uu____8048 :: uu____8074 in
                                    uu____8013 :: uu____8039 in
                                  uu____7978 :: uu____8004 in
                                uu____7947 :: uu____7969 in
                              uu____7912 :: uu____7938 in
                            uu____7877 :: uu____7903 in
                          uu____7842 :: uu____7868 in
                        uu____7807 :: uu____7833 in
                      uu____7772 :: uu____7798 in
                    uu____7741 :: uu____7763 in
                  uu____7711 :: uu____7732 in
                let mk1 l v1 =
                  let uu____8332 =
                    let uu____8337 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8369  ->
                              match uu____8369 with
                              | (l',uu____8378) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8337
                      (FStar_Option.map
                         (fun uu____8411  ->
                            match uu____8411 with | (uu____8422,b) -> b v1)) in
                  FStar_All.pipe_right uu____8332 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8463  ->
                          match uu____8463 with
                          | (l',uu____8472) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string,FStar_SMTEncoding_Term.sort)
        FStar_Pervasives_Native.tuple2 Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____8498 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8498 with
        | (xxsym,xx) ->
            let uu____8503 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8503 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8511 =
                   let uu____8515 =
                     let uu____8516 =
                       let uu____8522 =
                         let uu____8523 =
                           let uu____8526 =
                             let uu____8527 =
                               let uu____8530 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8530) in
                             FStar_SMTEncoding_Util.mkEq uu____8527 in
                           (xx_has_type, uu____8526) in
                         FStar_SMTEncoding_Util.mkImp uu____8523 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8522) in
                     FStar_SMTEncoding_Util.mkForall uu____8516 in
                   let uu____8543 =
                     let uu____8544 =
                       let uu____8545 =
                         let uu____8546 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8546 in
                       Prims.strcat module_name uu____8545 in
                     varops.mk_unique uu____8544 in
                   (uu____8515, (FStar_Pervasives_Native.Some "pretyping"),
                     uu____8543) in
                 FStar_SMTEncoding_Util.mkAssume uu____8511)
let primitive_type_axioms:
  FStar_TypeChecker_Env.env ->
    FStar_Ident.lident ->
      Prims.string ->
        FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.decl Prims.list
  =
  let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
  let x = FStar_SMTEncoding_Util.mkFreeV xx in
  let yy = ("y", FStar_SMTEncoding_Term.Term_sort) in
  let y = FStar_SMTEncoding_Util.mkFreeV yy in
  let mk_unit env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let uu____8576 =
      let uu____8577 =
        let uu____8581 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8581, (FStar_Pervasives_Native.Some "unit typing"),
          "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8577 in
    let uu____8583 =
      let uu____8585 =
        let uu____8586 =
          let uu____8590 =
            let uu____8591 =
              let uu____8597 =
                let uu____8598 =
                  let uu____8601 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8601) in
                FStar_SMTEncoding_Util.mkImp uu____8598 in
              ([[typing_pred]], [xx], uu____8597) in
            mkForall_fuel uu____8591 in
          (uu____8590, (FStar_Pervasives_Native.Some "unit inversion"),
            "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8586 in
      [uu____8585] in
    uu____8576 :: uu____8583 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8629 =
      let uu____8630 =
        let uu____8634 =
          let uu____8635 =
            let uu____8641 =
              let uu____8644 =
                let uu____8646 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8646] in
              [uu____8644] in
            let uu____8649 =
              let uu____8650 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8650 tt in
            (uu____8641, [bb], uu____8649) in
          FStar_SMTEncoding_Util.mkForall uu____8635 in
        (uu____8634, (FStar_Pervasives_Native.Some "bool typing"),
          "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8630 in
    let uu____8661 =
      let uu____8663 =
        let uu____8664 =
          let uu____8668 =
            let uu____8669 =
              let uu____8675 =
                let uu____8676 =
                  let uu____8679 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8679) in
                FStar_SMTEncoding_Util.mkImp uu____8676 in
              ([[typing_pred]], [xx], uu____8675) in
            mkForall_fuel uu____8669 in
          (uu____8668, (FStar_Pervasives_Native.Some "bool inversion"),
            "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8664 in
      [uu____8663] in
    uu____8629 :: uu____8661 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8713 =
        let uu____8714 =
          let uu____8718 =
            let uu____8720 =
              let uu____8722 =
                let uu____8724 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8725 =
                  let uu____8727 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8727] in
                uu____8724 :: uu____8725 in
              tt :: uu____8722 in
            tt :: uu____8720 in
          ("Prims.Precedes", uu____8718) in
        FStar_SMTEncoding_Util.mkApp uu____8714 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8713 in
    let precedes_y_x =
      let uu____8730 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8730 in
    let uu____8732 =
      let uu____8733 =
        let uu____8737 =
          let uu____8738 =
            let uu____8744 =
              let uu____8747 =
                let uu____8749 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8749] in
              [uu____8747] in
            let uu____8752 =
              let uu____8753 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8753 tt in
            (uu____8744, [bb], uu____8752) in
          FStar_SMTEncoding_Util.mkForall uu____8738 in
        (uu____8737, (FStar_Pervasives_Native.Some "int typing"),
          "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8733 in
    let uu____8764 =
      let uu____8766 =
        let uu____8767 =
          let uu____8771 =
            let uu____8772 =
              let uu____8778 =
                let uu____8779 =
                  let uu____8782 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8782) in
                FStar_SMTEncoding_Util.mkImp uu____8779 in
              ([[typing_pred]], [xx], uu____8778) in
            mkForall_fuel uu____8772 in
          (uu____8771, (FStar_Pervasives_Native.Some "int inversion"),
            "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8767 in
      let uu____8795 =
        let uu____8797 =
          let uu____8798 =
            let uu____8802 =
              let uu____8803 =
                let uu____8809 =
                  let uu____8810 =
                    let uu____8813 =
                      let uu____8814 =
                        let uu____8816 =
                          let uu____8818 =
                            let uu____8820 =
                              let uu____8821 =
                                let uu____8824 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8825 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8824, uu____8825) in
                              FStar_SMTEncoding_Util.mkGT uu____8821 in
                            let uu____8826 =
                              let uu____8828 =
                                let uu____8829 =
                                  let uu____8832 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8833 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8832, uu____8833) in
                                FStar_SMTEncoding_Util.mkGTE uu____8829 in
                              let uu____8834 =
                                let uu____8836 =
                                  let uu____8837 =
                                    let uu____8840 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8841 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8840, uu____8841) in
                                  FStar_SMTEncoding_Util.mkLT uu____8837 in
                                [uu____8836] in
                              uu____8828 :: uu____8834 in
                            uu____8820 :: uu____8826 in
                          typing_pred_y :: uu____8818 in
                        typing_pred :: uu____8816 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8814 in
                    (uu____8813, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8810 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8809) in
              mkForall_fuel uu____8803 in
            (uu____8802,
              (FStar_Pervasives_Native.Some
                 "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8798 in
        [uu____8797] in
      uu____8766 :: uu____8795 in
    uu____8732 :: uu____8764 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8871 =
      let uu____8872 =
        let uu____8876 =
          let uu____8877 =
            let uu____8883 =
              let uu____8886 =
                let uu____8888 = FStar_SMTEncoding_Term.boxString b in
                [uu____8888] in
              [uu____8886] in
            let uu____8891 =
              let uu____8892 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8892 tt in
            (uu____8883, [bb], uu____8891) in
          FStar_SMTEncoding_Util.mkForall uu____8877 in
        (uu____8876, (FStar_Pervasives_Native.Some "string typing"),
          "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8872 in
    let uu____8903 =
      let uu____8905 =
        let uu____8906 =
          let uu____8910 =
            let uu____8911 =
              let uu____8917 =
                let uu____8918 =
                  let uu____8921 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8921) in
                FStar_SMTEncoding_Util.mkImp uu____8918 in
              ([[typing_pred]], [xx], uu____8917) in
            mkForall_fuel uu____8911 in
          (uu____8910, (FStar_Pervasives_Native.Some "string inversion"),
            "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8906 in
      [uu____8905] in
    uu____8871 :: uu____8903 in
  let mk_ref1 env reft_name uu____8943 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8954 =
        let uu____8958 =
          let uu____8960 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8960] in
        (reft_name, uu____8958) in
      FStar_SMTEncoding_Util.mkApp uu____8954 in
    let refb =
      let uu____8963 =
        let uu____8967 =
          let uu____8969 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8969] in
        (reft_name, uu____8967) in
      FStar_SMTEncoding_Util.mkApp uu____8963 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8973 =
      let uu____8974 =
        let uu____8978 =
          let uu____8979 =
            let uu____8985 =
              let uu____8986 =
                let uu____8989 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8989) in
              FStar_SMTEncoding_Util.mkImp uu____8986 in
            ([[typing_pred]], [xx; aa], uu____8985) in
          mkForall_fuel uu____8979 in
        (uu____8978, (FStar_Pervasives_Native.Some "ref inversion"),
          "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8974 in
    [uu____8973] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (FStar_Pervasives_Native.Some "True interpretation"),
         "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9029 =
      let uu____9030 =
        let uu____9034 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9034, (FStar_Pervasives_Native.Some "False interpretation"),
          "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9030 in
    [uu____9029] in
  let mk_and_interp env conj uu____9045 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9062 =
      let uu____9063 =
        let uu____9067 =
          let uu____9068 =
            let uu____9074 =
              let uu____9075 =
                let uu____9078 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9078, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9075 in
            ([[l_and_a_b]], [aa; bb], uu____9074) in
          FStar_SMTEncoding_Util.mkForall uu____9068 in
        (uu____9067, (FStar_Pervasives_Native.Some "/\\ interpretation"),
          "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9063 in
    [uu____9062] in
  let mk_or_interp env disj uu____9102 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9119 =
      let uu____9120 =
        let uu____9124 =
          let uu____9125 =
            let uu____9131 =
              let uu____9132 =
                let uu____9135 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9135, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9132 in
            ([[l_or_a_b]], [aa; bb], uu____9131) in
          FStar_SMTEncoding_Util.mkForall uu____9125 in
        (uu____9124, (FStar_Pervasives_Native.Some "\\/ interpretation"),
          "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9120 in
    [uu____9119] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9176 =
      let uu____9177 =
        let uu____9181 =
          let uu____9182 =
            let uu____9188 =
              let uu____9189 =
                let uu____9192 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9192, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9189 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9188) in
          FStar_SMTEncoding_Util.mkForall uu____9182 in
        (uu____9181, (FStar_Pervasives_Native.Some "Eq2 interpretation"),
          "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9177 in
    [uu____9176] in
  let mk_eq3_interp env eq3 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq3_x_y = FStar_SMTEncoding_Util.mkApp (eq3, [a; b; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq3_x_y]) in
    let uu____9239 =
      let uu____9240 =
        let uu____9244 =
          let uu____9245 =
            let uu____9251 =
              let uu____9252 =
                let uu____9255 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9255, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9252 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9251) in
          FStar_SMTEncoding_Util.mkForall uu____9245 in
        (uu____9244, (FStar_Pervasives_Native.Some "Eq3 interpretation"),
          "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9240 in
    [uu____9239] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9300 =
      let uu____9301 =
        let uu____9305 =
          let uu____9306 =
            let uu____9312 =
              let uu____9313 =
                let uu____9316 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9316, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9313 in
            ([[l_imp_a_b]], [aa; bb], uu____9312) in
          FStar_SMTEncoding_Util.mkForall uu____9306 in
        (uu____9305, (FStar_Pervasives_Native.Some "==> interpretation"),
          "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9301 in
    [uu____9300] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9357 =
      let uu____9358 =
        let uu____9362 =
          let uu____9363 =
            let uu____9369 =
              let uu____9370 =
                let uu____9373 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9373, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9370 in
            ([[l_iff_a_b]], [aa; bb], uu____9369) in
          FStar_SMTEncoding_Util.mkForall uu____9363 in
        (uu____9362, (FStar_Pervasives_Native.Some "<==> interpretation"),
          "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9358 in
    [uu____9357] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9407 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9407 in
    let uu____9409 =
      let uu____9410 =
        let uu____9414 =
          let uu____9415 =
            let uu____9421 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9421) in
          FStar_SMTEncoding_Util.mkForall uu____9415 in
        (uu____9414, (FStar_Pervasives_Native.Some "not interpretation"),
          "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9410 in
    [uu____9409] in
  let mk_forall_interp env for_all1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_forall_a_b = FStar_SMTEncoding_Util.mkApp (for_all1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_forall_a_b]) in
    let valid_b_x =
      let uu____9461 =
        let uu____9465 =
          let uu____9467 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9467] in
        ("Valid", uu____9465) in
      FStar_SMTEncoding_Util.mkApp uu____9461 in
    let uu____9469 =
      let uu____9470 =
        let uu____9474 =
          let uu____9475 =
            let uu____9481 =
              let uu____9482 =
                let uu____9485 =
                  let uu____9486 =
                    let uu____9492 =
                      let uu____9495 =
                        let uu____9497 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9497] in
                      [uu____9495] in
                    let uu____9500 =
                      let uu____9501 =
                        let uu____9504 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9504, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9501 in
                    (uu____9492, [xx1], uu____9500) in
                  FStar_SMTEncoding_Util.mkForall uu____9486 in
                (uu____9485, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9482 in
            ([[l_forall_a_b]], [aa; bb], uu____9481) in
          FStar_SMTEncoding_Util.mkForall uu____9475 in
        (uu____9474, (FStar_Pervasives_Native.Some "forall interpretation"),
          "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9470 in
    [uu____9469] in
  let mk_exists_interp env for_some1 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let l_exists_a_b = FStar_SMTEncoding_Util.mkApp (for_some1, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_exists_a_b]) in
    let valid_b_x =
      let uu____9555 =
        let uu____9559 =
          let uu____9561 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9561] in
        ("Valid", uu____9559) in
      FStar_SMTEncoding_Util.mkApp uu____9555 in
    let uu____9563 =
      let uu____9564 =
        let uu____9568 =
          let uu____9569 =
            let uu____9575 =
              let uu____9576 =
                let uu____9579 =
                  let uu____9580 =
                    let uu____9586 =
                      let uu____9589 =
                        let uu____9591 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9591] in
                      [uu____9589] in
                    let uu____9594 =
                      let uu____9595 =
                        let uu____9598 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9598, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9595 in
                    (uu____9586, [xx1], uu____9594) in
                  FStar_SMTEncoding_Util.mkExists uu____9580 in
                (uu____9579, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9576 in
            ([[l_exists_a_b]], [aa; bb], uu____9575) in
          FStar_SMTEncoding_Util.mkForall uu____9569 in
        (uu____9568, (FStar_Pervasives_Native.Some "exists interpretation"),
          "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9564 in
    [uu____9563] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9634 =
      let uu____9635 =
        let uu____9639 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9640 = varops.mk_unique "typing_range_const" in
        (uu____9639, (FStar_Pervasives_Native.Some "Range_const typing"),
          uu____9640) in
      FStar_SMTEncoding_Util.mkAssume uu____9635 in
    [uu____9634] in
  let prims1 =
    [(FStar_Parser_Const.unit_lid, mk_unit);
    (FStar_Parser_Const.bool_lid, mk_bool);
    (FStar_Parser_Const.int_lid, mk_int);
    (FStar_Parser_Const.string_lid, mk_str);
    (FStar_Parser_Const.ref_lid, mk_ref1);
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
    (FStar_Parser_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____9902 =
            FStar_Util.find_opt
              (fun uu____9920  ->
                 match uu____9920 with
                 | (l,uu____9930) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9902 with
          | FStar_Pervasives_Native.None  -> []
          | FStar_Pervasives_Native.Some (uu____9952,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9989 = encode_function_type_as_formula t env in
        match uu____9989 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form,
                   (FStar_Pervasives_Native.Some
                      (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list,env_t)
              FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____10021 =
              (let uu____10022 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10022) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10021
            then
              let uu____10026 = new_term_constant_and_tok_from_lid env lid in
              match uu____10026 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10038 =
                      let uu____10039 = FStar_Syntax_Subst.compress t_norm in
                      uu____10039.FStar_Syntax_Syntax.n in
                    match uu____10038 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10044) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10061  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10064 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (FStar_Pervasives_Native.Some
                           "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____10073 = prims.is lid in
               if uu____10073
               then
                 let vname = varops.new_fvar lid in
                 let uu____10078 = prims.mk lid vname in
                 match uu____10078 with
                 | (tok,definition) ->
                     let env1 =
                       push_free_var env lid vname
                         (FStar_Pervasives_Native.Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10093 =
                    let uu____10099 = curried_arrow_formals_comp t_norm in
                    match uu____10099 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10110 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10110
                          then
                            let uu____10111 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10112 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10112.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10112.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10112.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10112.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10112.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10112.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10112.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10112.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10112.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10112.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10112.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10112.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10112.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10112.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10112.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10112.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10112.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10112.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10112.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10112.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10112.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10112.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10112.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10111
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10119 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10119)
                        else
                          (args,
                            (FStar_Pervasives_Native.None,
                              (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10093 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10146 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10146 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10159 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10183  ->
                                     match uu___115_10183 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10186 =
                                           FStar_Util.prefix vars in
                                         (match uu____10186 with
                                          | (uu____10197,(xxsym,uu____10199))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10209 =
                                                let uu____10210 =
                                                  let uu____10214 =
                                                    let uu____10215 =
                                                      let uu____10221 =
                                                        let uu____10222 =
                                                          let uu____10225 =
                                                            let uu____10226 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10226 in
                                                          (vapp, uu____10225) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10222 in
                                                      ([[vapp]], vars,
                                                        uu____10221) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10215 in
                                                  (uu____10214,
                                                    (FStar_Pervasives_Native.Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10210 in
                                              [uu____10209])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10237 =
                                           FStar_Util.prefix vars in
                                         (match uu____10237 with
                                          | (uu____10248,(xxsym,uu____10250))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let f1 =
                                                {
                                                  FStar_Syntax_Syntax.ppname
                                                    = f;
                                                  FStar_Syntax_Syntax.index =
                                                    (Prims.parse_int "0");
                                                  FStar_Syntax_Syntax.sort =
                                                    FStar_Syntax_Syntax.tun
                                                } in
                                              let tp_name =
                                                mk_term_projector_name d f1 in
                                              let prim_app =
                                                FStar_SMTEncoding_Util.mkApp
                                                  (tp_name, [xx]) in
                                              let uu____10264 =
                                                let uu____10265 =
                                                  let uu____10269 =
                                                    let uu____10270 =
                                                      let uu____10276 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10276) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10270 in
                                                  (uu____10269,
                                                    (FStar_Pervasives_Native.Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10265 in
                                              [uu____10264])
                                     | uu____10285 -> [])) in
                           let uu____10286 =
                             encode_binders FStar_Pervasives_Native.None
                               formals env1 in
                           (match uu____10286 with
                            | (vars,guards,env',decls1,uu____10302) ->
                                let uu____10309 =
                                  match pre_opt with
                                  | FStar_Pervasives_Native.None  ->
                                      let uu____10314 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10314, decls1)
                                  | FStar_Pervasives_Native.Some p ->
                                      let uu____10316 = encode_formula p env' in
                                      (match uu____10316 with
                                       | (g,ds) ->
                                           let uu____10323 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10323,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10309 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10332 =
                                         let uu____10336 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10336) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10332 in
                                     let uu____10341 =
                                       let vname_decl =
                                         let uu____10346 =
                                           let uu____10352 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10357  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10352,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             FStar_Pervasives_Native.None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10346 in
                                       let uu____10362 =
                                         let env2 =
                                           let uu___145_10366 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10366.bindings);
                                             depth = (uu___145_10366.depth);
                                             tcenv = (uu___145_10366.tcenv);
                                             warn = (uu___145_10366.warn);
                                             cache = (uu___145_10366.cache);
                                             nolabels =
                                               (uu___145_10366.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10366.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10366.current_module_name)
                                           } in
                                         let uu____10367 =
                                           let uu____10368 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10368 in
                                         if uu____10367
                                         then
                                           encode_term_pred
                                             FStar_Pervasives_Native.None tt
                                             env2 vtok_tm
                                         else
                                           encode_term_pred
                                             FStar_Pervasives_Native.None
                                             t_norm env2 vtok_tm in
                                       match uu____10362 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10378::uu____10379 ->
                                                 let ff =
                                                   ("ty",
                                                     FStar_SMTEncoding_Term.Term_sort) in
                                                 let f =
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                     ff in
                                                 let vtok_app_l =
                                                   mk_Apply vtok_tm [ff] in
                                                 let vtok_app_r =
                                                   mk_Apply f
                                                     [(vtok,
                                                        FStar_SMTEncoding_Term.Term_sort)] in
                                                 let guarded_tok_typing =
                                                   let uu____10402 =
                                                     let uu____10408 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10408) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10402 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10422 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (FStar_Pervasives_Native.Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10424 =
                                             match formals with
                                             | [] ->
                                                 let uu____10433 =
                                                   let uu____10434 =
                                                     let uu____10436 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          FStar_Pervasives_Native.Some
                                                            _0_34)
                                                       uu____10436 in
                                                   push_free_var env1 lid
                                                     vname uu____10434 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10433)
                                             | uu____10439 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       FStar_Pervasives_Native.None) in
                                                 let vtok_fresh =
                                                   let uu____10444 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10444 in
                                                 let name_tok_corr =
                                                   let uu____10446 =
                                                     let uu____10450 =
                                                       let uu____10451 =
                                                         let uu____10457 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10457) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10451 in
                                                     (uu____10450,
                                                       (FStar_Pervasives_Native.Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10446 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10424 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10341 with
                                      | (decls2,env2) ->
                                          let uu____10481 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10486 =
                                              encode_term res_t1 env' in
                                            match uu____10486 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10494 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10494,
                                                  decls) in
                                          (match uu____10481 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10502 =
                                                   let uu____10506 =
                                                     let uu____10507 =
                                                       let uu____10513 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10513) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10507 in
                                                   (uu____10506,
                                                     (FStar_Pervasives_Native.Some
                                                        "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10502 in
                                               let freshness =
                                                 let uu____10522 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10522
                                                 then
                                                   let uu____10525 =
                                                     let uu____10526 =
                                                       let uu____10532 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives_Native.snd) in
                                                       let uu____10538 =
                                                         varops.next_id () in
                                                       (vname, uu____10532,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10538) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10526 in
                                                   let uu____10540 =
                                                     let uu____10542 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10542] in
                                                   uu____10525 :: uu____10540
                                                 else [] in
                                               let g =
                                                 let uu____10546 =
                                                   let uu____10548 =
                                                     let uu____10550 =
                                                       let uu____10552 =
                                                         let uu____10554 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10554 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10552 in
                                                     FStar_List.append decls3
                                                       uu____10550 in
                                                   FStar_List.append decls2
                                                     uu____10548 in
                                                 FStar_List.append decls11
                                                   uu____10546 in
                                               (g, env2))))))))
let declare_top_level_let:
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
          let uu____10576 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10576 with
          | FStar_Pervasives_Native.None  ->
              let uu____10599 = encode_free_var env x t t_norm [] in
              (match uu____10599 with
               | (decls,env1) ->
                   let uu____10614 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10614 with
                    | (n1,x',uu____10633) -> ((n1, x'), decls, env1)))
          | FStar_Pervasives_Native.Some (n1,x1,uu____10645) ->
              ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list,env_t)
            FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____10678 = encode_free_var env lid t tt quals in
          match uu____10678 with
          | (decls,env1) ->
              let uu____10689 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10689
              then
                let uu____10693 =
                  let uu____10695 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10695 in
                (uu____10693, env1)
              else (decls, env1)
let encode_top_level_vals:
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
             (fun uu____10723  ->
                fun lb  ->
                  match uu____10723 with
                  | (decls,env1) ->
                      let uu____10735 =
                        let uu____10739 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10739
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10735 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Parser_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10753 = FStar_Syntax_Util.head_and_args t in
    match uu____10753 with
    | (hd1,args) ->
        let uu____10779 =
          let uu____10780 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10780.FStar_Syntax_Syntax.n in
        (match uu____10779 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10784,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10797 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool,FStar_Syntax_Syntax.letbinding Prims.list)
      FStar_Pervasives_Native.tuple2 ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list,env_t)
          FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun uu____10812  ->
      fun quals  ->
        match uu____10812 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10861 = FStar_Util.first_N nbinders formals in
              match uu____10861 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10901  ->
                         fun uu____10902  ->
                           match (uu____10901, uu____10902) with
                           | ((formal,uu____10912),(binder,uu____10914)) ->
                               let uu____10919 =
                                 let uu____10924 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10924) in
                               FStar_Syntax_Syntax.NT uu____10919) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10929 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10943  ->
                              match uu____10943 with
                              | (x,i) ->
                                  let uu____10950 =
                                    let uu___146_10951 = x in
                                    let uu____10952 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_10951.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_10951.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10952
                                    } in
                                  (uu____10950, i))) in
                    FStar_All.pipe_right uu____10929
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10964 =
                      let uu____10966 =
                        let uu____10967 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10967.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left
                        (fun _0_35  -> FStar_Pervasives_Native.Some _0_35)
                        uu____10966 in
                    let uu____10971 =
                      let uu____10972 = FStar_Syntax_Subst.compress body in
                      let uu____10973 =
                        let uu____10974 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives_Native.snd
                          uu____10974 in
                      FStar_Syntax_Syntax.extend_app_n uu____10972
                        uu____10973 in
                    uu____10971 uu____10964 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11016 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11016
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11017 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11017.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11017.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11017.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11017.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11017.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11017.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11017.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11017.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11017.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11017.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11017.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11017.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11017.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11017.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11017.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11017.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11017.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11017.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11017.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11017.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11017.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11017.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11017.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11038 = FStar_Syntax_Util.abs_formals e in
                match uu____11038 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11087::uu____11088 ->
                         let uu____11096 =
                           let uu____11097 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11097.FStar_Syntax_Syntax.n in
                         (match uu____11096 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11124 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11124 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11150 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11150
                                   then
                                     let uu____11168 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11168 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11214  ->
                                                   fun uu____11215  ->
                                                     match (uu____11214,
                                                             uu____11215)
                                                     with
                                                     | ((x,uu____11225),
                                                        (b,uu____11227)) ->
                                                         let uu____11232 =
                                                           let uu____11237 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11237) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11232)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11239 =
                                            let uu____11250 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11250) in
                                          (uu____11239, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11285 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11285 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11337) ->
                              let uu____11342 =
                                let uu____11353 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                FStar_Pervasives_Native.fst uu____11353 in
                              (uu____11342, true)
                          | uu____11386 when Prims.op_Negation norm1 ->
                              let t_norm2 =
                                FStar_TypeChecker_Normalize.normalize
                                  [FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                                  FStar_TypeChecker_Normalize.Beta;
                                  FStar_TypeChecker_Normalize.WHNF;
                                  FStar_TypeChecker_Normalize.Exclude
                                    FStar_TypeChecker_Normalize.Zeta;
                                  FStar_TypeChecker_Normalize.UnfoldUntil
                                    FStar_Syntax_Syntax.Delta_constant;
                                  FStar_TypeChecker_Normalize.EraseUniverses]
                                  env.tcenv t_norm1 in
                              aux true t_norm2
                          | uu____11388 ->
                              let uu____11389 =
                                let uu____11390 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11391 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11390
                                  uu____11391 in
                              failwith uu____11389)
                     | uu____11404 ->
                         let uu____11405 =
                           let uu____11406 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11406.FStar_Syntax_Syntax.n in
                         (match uu____11405 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11433 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11433 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11451 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11451 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11499 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11527 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11527
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11534 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11575  ->
                            fun lb  ->
                              match uu____11575 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11626 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11626
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11629 =
                                      let uu____11637 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11637
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11629 with
                                    | (tok,decl,env2) ->
                                        let uu____11662 =
                                          let uu____11669 =
                                            let uu____11675 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11675, tok) in
                                          uu____11669 :: toks in
                                        (uu____11662, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11534 with
                  | (toks,typs,decls,env1) ->
                      let toks1 = FStar_List.rev toks in
                      let decls1 =
                        FStar_All.pipe_right (FStar_List.rev decls)
                          FStar_List.flatten in
                      let typs1 = FStar_List.rev typs in
                      let mk_app1 curry f ftok vars =
                        match vars with
                        | [] ->
                            FStar_SMTEncoding_Util.mkFreeV
                              (f, FStar_SMTEncoding_Term.Term_sort)
                        | uu____11777 ->
                            if curry
                            then
                              (match ftok with
                               | FStar_Pervasives_Native.Some ftok1 ->
                                   mk_Apply ftok1 vars
                               | FStar_Pervasives_Native.None  ->
                                   let uu____11782 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11782 vars)
                            else
                              (let uu____11784 =
                                 let uu____11788 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11788) in
                               FStar_SMTEncoding_Util.mkApp uu____11784) in
                      let uu____11793 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11795  ->
                                 match uu___116_11795 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11796 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11799 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11799))) in
                      if uu____11793
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11819;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11821;
                                FStar_Syntax_Syntax.lbeff = uu____11822;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11863 =
                                 let uu____11867 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11867 with
                                 | (tcenv',uu____11878,e_t) ->
                                     let uu____11882 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11889 -> failwith "Impossible" in
                                     (match uu____11882 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_11898 = env1 in
                                            {
                                              bindings =
                                                (uu___150_11898.bindings);
                                              depth = (uu___150_11898.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_11898.warn);
                                              cache = (uu___150_11898.cache);
                                              nolabels =
                                                (uu___150_11898.nolabels);
                                              use_zfuel_name =
                                                (uu___150_11898.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_11898.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_11898.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11863 with
                                | (env',e1,t_norm1) ->
                                    let uu____11905 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11905 with
                                     | ((binders,body,uu____11917,uu____11918),curry)
                                         ->
                                         ((let uu____11925 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11925
                                           then
                                             let uu____11926 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11927 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11926 uu____11927
                                           else ());
                                          (let uu____11929 =
                                             encode_binders
                                               FStar_Pervasives_Native.None
                                               binders env' in
                                           match uu____11929 with
                                           | (vars,guards,env'1,binder_decls,uu____11945)
                                               ->
                                               let body1 =
                                                 let uu____11953 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11953
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11956 =
                                                 let uu____11961 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11961
                                                 then
                                                   let uu____11967 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11968 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11967, uu____11968)
                                                 else
                                                   (let uu____11974 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11974)) in
                                               (match uu____11956 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11988 =
                                                        let uu____11992 =
                                                          let uu____11993 =
                                                            let uu____11999 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11999) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11993 in
                                                        let uu____12005 =
                                                          let uu____12007 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          FStar_Pervasives_Native.Some
                                                            uu____12007 in
                                                        (uu____11992,
                                                          uu____12005,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11988 in
                                                    let uu____12009 =
                                                      let uu____12011 =
                                                        let uu____12013 =
                                                          let uu____12015 =
                                                            let uu____12017 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12017 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12015 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12013 in
                                                      FStar_List.append
                                                        decls1 uu____12011 in
                                                    (uu____12009, env1))))))
                           | uu____12020 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12039 = varops.fresh "fuel" in
                             (uu____12039, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12042 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12081  ->
                                     fun uu____12082  ->
                                       match (uu____12081, uu____12082) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12164 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12164 in
                                           let gtok =
                                             let uu____12166 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12166 in
                                           let env3 =
                                             let uu____12168 =
                                               let uu____12170 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  ->
                                                    FStar_Pervasives_Native.Some
                                                      _0_36) uu____12170 in
                                             push_free_var env2 flid gtok
                                               uu____12168 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12042 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12256
                                 t_norm uu____12258 =
                                 match (uu____12256, uu____12258) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12285;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12286;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12303 =
                                       let uu____12307 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12307 with
                                       | (tcenv',uu____12322,e_t) ->
                                           let uu____12326 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12333 ->
                                                 failwith "Impossible" in
                                           (match uu____12326 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12342 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12342.bindings);
                                                    depth =
                                                      (uu___151_12342.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12342.warn);
                                                    cache =
                                                      (uu___151_12342.cache);
                                                    nolabels =
                                                      (uu___151_12342.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12342.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12342.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12342.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12303 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12352 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12352
                                            then
                                              let uu____12353 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12354 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12355 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12353 uu____12354
                                                uu____12355
                                            else ());
                                           (let uu____12357 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12357 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12379 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12379
                                                  then
                                                    let uu____12380 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12381 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12382 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12383 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12380 uu____12381
                                                      uu____12382 uu____12383
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12387 =
                                                    encode_binders
                                                      FStar_Pervasives_Native.None
                                                      binders env' in
                                                  match uu____12387 with
                                                  | (vars,guards,env'1,binder_decls,uu____12405)
                                                      ->
                                                      let decl_g =
                                                        let uu____12413 =
                                                          let uu____12419 =
                                                            let uu____12421 =
                                                              FStar_List.map
                                                                FStar_Pervasives_Native.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12421 in
                                                          (g, uu____12419,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12413 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (FStar_Pervasives_Native.Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____12436 =
                                                          let uu____12440 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12440) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12436 in
                                                      let gsapp =
                                                        let uu____12446 =
                                                          let uu____12450 =
                                                            let uu____12452 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12452 ::
                                                              vars_tm in
                                                          (g, uu____12450) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12446 in
                                                      let gmax =
                                                        let uu____12456 =
                                                          let uu____12460 =
                                                            let uu____12462 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12462 ::
                                                              vars_tm in
                                                          (g, uu____12460) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12456 in
                                                      let body1 =
                                                        let uu____12466 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12466
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12468 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12468 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12479
                                                               =
                                                               let uu____12483
                                                                 =
                                                                 let uu____12484
                                                                   =
                                                                   let uu____12492
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (FStar_Pervasives_Native.Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12492) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12484 in
                                                               let uu____12503
                                                                 =
                                                                 let uu____12505
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 FStar_Pervasives_Native.Some
                                                                   uu____12505 in
                                                               (uu____12483,
                                                                 uu____12503,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12479 in
                                                           let eqn_f =
                                                             let uu____12508
                                                               =
                                                               let uu____12512
                                                                 =
                                                                 let uu____12513
                                                                   =
                                                                   let uu____12519
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12519) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12513 in
                                                               (uu____12512,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12508 in
                                                           let eqn_g' =
                                                             let uu____12527
                                                               =
                                                               let uu____12531
                                                                 =
                                                                 let uu____12532
                                                                   =
                                                                   let uu____12538
                                                                    =
                                                                    let uu____12539
                                                                    =
                                                                    let uu____12542
                                                                    =
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12547
                                                                    =
                                                                    let uu____12549
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12549
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12547) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12543 in
                                                                    (gsapp,
                                                                    uu____12542) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12539 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12538) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12532 in
                                                               (uu____12531,
                                                                 (FStar_Pervasives_Native.Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12527 in
                                                           let uu____12561 =
                                                             let uu____12566
                                                               =
                                                               encode_binders
                                                                 FStar_Pervasives_Native.None
                                                                 formals
                                                                 env02 in
                                                             match uu____12566
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12583)
                                                                 ->
                                                                 let vars_tm1
                                                                   =
                                                                   FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars1 in
                                                                 let gapp =
                                                                   FStar_SMTEncoding_Util.mkApp
                                                                    (g,
                                                                    (fuel_tm
                                                                    ::
                                                                    vars_tm1)) in
                                                                 let tok_corr
                                                                   =
                                                                   let tok_app
                                                                    =
                                                                    let uu____12598
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12598
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12601
                                                                    =
                                                                    let uu____12605
                                                                    =
                                                                    let uu____12606
                                                                    =
                                                                    let uu____12612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12612) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12606 in
                                                                    (uu____12605,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12601 in
                                                                 let uu____12623
                                                                   =
                                                                   let uu____12627
                                                                    =
                                                                    encode_term_pred
                                                                    FStar_Pervasives_Native.None
                                                                    tres env3
                                                                    gapp in
                                                                   match uu____12627
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12635
                                                                    =
                                                                    let uu____12637
                                                                    =
                                                                    let uu____12638
                                                                    =
                                                                    let uu____12642
                                                                    =
                                                                    let uu____12643
                                                                    =
                                                                    let uu____12649
                                                                    =
                                                                    let uu____12650
                                                                    =
                                                                    let uu____12653
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12653,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12650 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12649) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12643 in
                                                                    (uu____12642,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12638 in
                                                                    [uu____12637] in
                                                                    (d3,
                                                                    uu____12635) in
                                                                 (match uu____12623
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12561
                                                            with
                                                            | (aux_decls,g_typing)
                                                                ->
                                                                ((FStar_List.append
                                                                    binder_decls
                                                                    (
                                                                    FStar_List.append
                                                                    decls2
                                                                    (FStar_List.append
                                                                    aux_decls
                                                                    [decl_g;
                                                                    decl_g_tok]))),
                                                                  (FStar_List.append
                                                                    [eqn_g;
                                                                    eqn_g';
                                                                    eqn_f]
                                                                    g_typing),
                                                                  env02)))))))) in
                               let uu____12688 =
                                 let uu____12695 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12731  ->
                                      fun uu____12732  ->
                                        match (uu____12731, uu____12732) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12818 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12818 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12695 in
                               (match uu____12688 with
                                | (decls2,eqns,env01) ->
                                    let uu____12858 =
                                      let isDeclFun uu___117_12866 =
                                        match uu___117_12866 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12867 -> true
                                        | uu____12873 -> false in
                                      let uu____12874 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12874
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12858 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12901 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12901
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12934 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12934 with
        | FStar_Pervasives_Native.None  -> ""
        | FStar_Pervasives_Native.Some l -> l.FStar_Ident.str in
      let uu____12937 = encode_sigelt' env se in
      match uu____12937 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12947 =
                  let uu____12948 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12948 in
                [uu____12947]
            | uu____12949 ->
                let uu____12950 =
                  let uu____12952 =
                    let uu____12953 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12953 in
                  uu____12952 :: g in
                let uu____12954 =
                  let uu____12956 =
                    let uu____12957 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12957 in
                  [uu____12956] in
                FStar_List.append uu____12950 uu____12954 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12965 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____12968 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____12970 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____12972 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____12980 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12983 =
            let uu____12984 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12984 Prims.op_Negation in
          if uu____12983
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13004 ->
                   let uu____13005 =
                     let uu____13008 =
                       let uu____13009 =
                         let uu____13024 =
                           FStar_All.pipe_left
                             (fun _0_37  ->
                                FStar_Pervasives_Native.Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Parser_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13024) in
                       FStar_Syntax_Syntax.Tm_abs uu____13009 in
                     FStar_Syntax_Syntax.mk uu____13008 in
                   uu____13005 FStar_Pervasives_Native.None
                     tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13077 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13077 with
               | (aname,atok,env2) ->
                   let uu____13087 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13087 with
                    | (formals,uu____13097) ->
                        let uu____13104 =
                          let uu____13107 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13107 env2 in
                        (match uu____13104 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13115 =
                                 let uu____13116 =
                                   let uu____13122 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13130  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13122,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (FStar_Pervasives_Native.Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13116 in
                               [uu____13115;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (FStar_Pervasives_Native.Some
                                      "Action token"))] in
                             let uu____13137 =
                               let aux uu____13166 uu____13167 =
                                 match (uu____13166, uu____13167) with
                                 | ((bv,uu____13194),(env3,acc_sorts,acc)) ->
                                     let uu____13215 = gen_term_var env3 bv in
                                     (match uu____13215 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13137 with
                              | (uu____13253,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13267 =
                                      let uu____13271 =
                                        let uu____13272 =
                                          let uu____13278 =
                                            let uu____13279 =
                                              let uu____13282 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13282) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13279 in
                                          ([[app]], xs_sorts, uu____13278) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13272 in
                                      (uu____13271,
                                        (FStar_Pervasives_Native.Some
                                           "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13267 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13294 =
                                      let uu____13298 =
                                        let uu____13299 =
                                          let uu____13305 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13305) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13299 in
                                      (uu____13298,
                                        (FStar_Pervasives_Native.Some
                                           "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13294 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13315 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13315 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13331,uu____13332)
          when FStar_Ident.lid_equals lid FStar_Parser_Const.precedes_lid ->
          let uu____13333 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13333 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13344,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13349 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13351  ->
                      match uu___118_13351 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13352 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13355 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13356 -> false)) in
            Prims.op_Negation uu____13349 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant
                 FStar_Pervasives_Native.None in
             let uu____13362 = encode_top_level_val env fv t quals in
             match uu____13362 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13374 =
                   let uu____13376 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13376 in
                 (uu____13374, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13381 = encode_formula f env in
          (match uu____13381 with
           | (f1,decls) ->
               let g =
                 let uu____13390 =
                   let uu____13391 =
                     let uu____13395 =
                       let uu____13397 =
                         let uu____13398 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13398 in
                       FStar_Pervasives_Native.Some uu____13397 in
                     let uu____13399 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13395, uu____13399) in
                   FStar_SMTEncoding_Util.mkAssume uu____13391 in
                 [uu____13390] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13403,uu____13404) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13410 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13417 =
                       let uu____13422 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13422.FStar_Syntax_Syntax.fv_name in
                     uu____13417.FStar_Syntax_Syntax.v in
                   let uu____13426 =
                     let uu____13427 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13427 in
                   if uu____13426
                   then
                     let val_decl =
                       let uu___152_13442 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13442.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13442.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13442.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13446 = encode_sigelt' env1 val_decl in
                     match uu____13446 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (FStar_Pervasives_Native.snd lbs) in
          (match uu____13410 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13463,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13465;
                          FStar_Syntax_Syntax.lbtyp = uu____13466;
                          FStar_Syntax_Syntax.lbeff = uu____13467;
                          FStar_Syntax_Syntax.lbdef = uu____13468;_}::[]),uu____13469,uu____13470)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Parser_Const.b2t_lid
          ->
          let uu____13484 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13484 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13507 =
                   let uu____13509 =
                     let uu____13510 =
                       let uu____13514 =
                         let uu____13515 =
                           let uu____13521 =
                             let uu____13522 =
                               let uu____13525 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13525) in
                             FStar_SMTEncoding_Util.mkEq uu____13522 in
                           ([[b2t_x]], [xx], uu____13521) in
                         FStar_SMTEncoding_Util.mkForall uu____13515 in
                       (uu____13514,
                         (FStar_Pervasives_Native.Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13510 in
                   [uu____13509] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort,
                      FStar_Pervasives_Native.None))
                   :: uu____13507 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13542,uu____13543,uu____13544)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13550  ->
                  match uu___119_13550 with
                  | FStar_Syntax_Syntax.Discriminator uu____13551 -> true
                  | uu____13552 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13554,lids,uu____13556) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13563 =
                     let uu____13564 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13564.FStar_Ident.idText in
                   uu____13563 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13566  ->
                     match uu___120_13566 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13567 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13570,uu____13571)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13581  ->
                  match uu___121_13581 with
                  | FStar_Syntax_Syntax.Projector uu____13582 -> true
                  | uu____13585 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13592 = try_lookup_free_var env l in
          (match uu____13592 with
           | FStar_Pervasives_Native.Some uu____13596 -> ([], env)
           | FStar_Pervasives_Native.None  ->
               let se1 =
                 let uu___153_13599 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13599.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13599.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13605,uu____13606) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13618) ->
          let uu____13623 = encode_sigelts env ses in
          (match uu____13623 with
           | (g,env1) ->
               let uu____13633 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13643  ->
                         match uu___122_13643 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13644;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 FStar_Pervasives_Native.Some
                                 "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13645;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13646;_}
                             -> false
                         | uu____13648 -> true)) in
               (match uu____13633 with
                | (g',inversions) ->
                    let uu____13657 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13667  ->
                              match uu___123_13667 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13668 ->
                                  true
                              | uu____13674 -> false)) in
                    (match uu____13657 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13685,tps,k,uu____13688,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13698  ->
                    match uu___124_13698 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13699 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13706 = c in
              match uu____13706 with
              | (name,args,uu____13710,uu____13711,uu____13712) ->
                  let uu____13715 =
                    let uu____13716 =
                      let uu____13722 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13729  ->
                                match uu____13729 with
                                | (uu____13733,sort,uu____13735) -> sort)) in
                      (name, uu____13722, FStar_SMTEncoding_Term.Term_sort,
                        FStar_Pervasives_Native.None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13716 in
                  [uu____13715]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13753 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13756 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13756 FStar_Option.isNone)) in
            if uu____13753
            then []
            else
              (let uu____13773 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13773 with
               | (xxsym,xx) ->
                   let uu____13779 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13790  ->
                             fun l  ->
                               match uu____13790 with
                               | (out,decls) ->
                                   let uu____13802 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13802 with
                                    | (uu____13808,data_t) ->
                                        let uu____13810 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13810 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13839 =
                                                 let uu____13840 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13840.FStar_Syntax_Syntax.n in
                                               match uu____13839 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13848,indices) ->
                                                   indices
                                               | uu____13864 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13876  ->
                                                         match uu____13876
                                                         with
                                                         | (x,uu____13880) ->
                                                             let uu____13881
                                                               =
                                                               let uu____13882
                                                                 =
                                                                 let uu____13886
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13886,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13882 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13881)
                                                    env) in
                                             let uu____13888 =
                                               encode_args indices env1 in
                                             (match uu____13888 with
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
                                                      let uu____13908 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13916
                                                                 =
                                                                 let uu____13919
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13919,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13916)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13908
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13921 =
                                                      let uu____13922 =
                                                        let uu____13925 =
                                                          let uu____13926 =
                                                            let uu____13929 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13929,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13926 in
                                                        (out, uu____13925) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13922 in
                                                    (uu____13921,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13779 with
                    | (data_ax,decls) ->
                        let uu____13937 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13937 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13948 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13948 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13951 =
                                 let uu____13955 =
                                   let uu____13956 =
                                     let uu____13962 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13970 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13962,
                                       uu____13970) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13956 in
                                 let uu____13978 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13955,
                                   (FStar_Pervasives_Native.Some
                                      "inversion axiom"), uu____13978) in
                               FStar_SMTEncoding_Util.mkAssume uu____13951 in
                             let pattern_guarded_inversion =
                               let uu____13982 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13982
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13990 =
                                   let uu____13991 =
                                     let uu____13995 =
                                       let uu____13996 =
                                         let uu____14002 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14010 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14002, uu____14010) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13996 in
                                     let uu____14018 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13995,
                                       (FStar_Pervasives_Native.Some
                                          "inversion axiom"), uu____14018) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13991 in
                                 [uu____13990]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14021 =
            let uu____14029 =
              let uu____14030 = FStar_Syntax_Subst.compress k in
              uu____14030.FStar_Syntax_Syntax.n in
            match uu____14029 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14059 -> (tps, k) in
          (match uu____14021 with
           | (formals,res) ->
               let uu____14074 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14074 with
                | (formals1,res1) ->
                    let uu____14081 =
                      encode_binders FStar_Pervasives_Native.None formals1
                        env in
                    (match uu____14081 with
                     | (vars,guards,env',binder_decls,uu____14096) ->
                         let uu____14103 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14103 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14116 =
                                  let uu____14120 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14120) in
                                FStar_SMTEncoding_Util.mkApp uu____14116 in
                              let uu____14125 =
                                let tname_decl =
                                  let uu____14131 =
                                    let uu____14132 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14147  ->
                                              match uu____14147 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14155 = varops.next_id () in
                                    (tname, uu____14132,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14155, false) in
                                  constructor_or_logic_type_decl uu____14131 in
                                let uu____14160 =
                                  match vars with
                                  | [] ->
                                      let uu____14167 =
                                        let uu____14168 =
                                          let uu____14170 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  ->
                                               FStar_Pervasives_Native.Some
                                                 _0_38) uu____14170 in
                                        push_free_var env1 t tname
                                          uu____14168 in
                                      ([], uu____14167)
                                  | uu____14174 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (FStar_Pervasives_Native.Some
                                               "token")) in
                                      let ttok_fresh =
                                        let uu____14180 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14180 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14189 =
                                          let uu____14193 =
                                            let uu____14194 =
                                              let uu____14202 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats,
                                                FStar_Pervasives_Native.None,
                                                vars, uu____14202) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14194 in
                                          (uu____14193,
                                            (FStar_Pervasives_Native.Some
                                               "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14189 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14160 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14125 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14225 =
                                       encode_term_pred
                                         FStar_Pervasives_Native.None res1
                                         env' tapp in
                                     match uu____14225 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14239 =
                                               let uu____14240 =
                                                 let uu____14244 =
                                                   let uu____14245 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14245 in
                                                 (uu____14244,
                                                   (FStar_Pervasives_Native.Some
                                                      "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14240 in
                                             [uu____14239]
                                           else [] in
                                         let uu____14248 =
                                           let uu____14250 =
                                             let uu____14252 =
                                               let uu____14253 =
                                                 let uu____14257 =
                                                   let uu____14258 =
                                                     let uu____14264 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14264) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14258 in
                                                 (uu____14257,
                                                   FStar_Pervasives_Native.None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14253 in
                                             [uu____14252] in
                                           FStar_List.append karr uu____14250 in
                                         FStar_List.append decls1 uu____14248 in
                                   let aux =
                                     let uu____14273 =
                                       let uu____14275 =
                                         inversion_axioms tapp vars in
                                       let uu____14277 =
                                         let uu____14279 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14279] in
                                       FStar_List.append uu____14275
                                         uu____14277 in
                                     FStar_List.append kindingAx uu____14273 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14284,uu____14285,uu____14286,uu____14287,uu____14288)
          when FStar_Ident.lid_equals d FStar_Parser_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14293,t,uu____14295,n_tps,uu____14297) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14302 = new_term_constant_and_tok_from_lid env d in
          (match uu____14302 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14313 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14313 with
                | (formals,t_res) ->
                    let uu____14335 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14335 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14344 =
                           encode_binders
                             (FStar_Pervasives_Native.Some fuel_tm) formals
                             env1 in
                         (match uu____14344 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14382 =
                                            mk_term_projector_name d x in
                                          (uu____14382,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14384 =
                                  let uu____14394 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14394, true) in
                                FStar_All.pipe_right uu____14384
                                  FStar_SMTEncoding_Term.constructor_to_decl in
                              let app = mk_Apply ddtok_tm vars in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let xvars =
                                FStar_List.map FStar_SMTEncoding_Util.mkFreeV
                                  vars in
                              let dapp =
                                FStar_SMTEncoding_Util.mkApp
                                  (ddconstrsym, xvars) in
                              let uu____14416 =
                                encode_term_pred FStar_Pervasives_Native.None
                                  t env1 ddtok_tm in
                              (match uu____14416 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14424::uu____14425 ->
                                         let ff =
                                           ("ty",
                                             FStar_SMTEncoding_Term.Term_sort) in
                                         let f =
                                           FStar_SMTEncoding_Util.mkFreeV ff in
                                         let vtok_app_l =
                                           mk_Apply ddtok_tm [ff] in
                                         let vtok_app_r =
                                           mk_Apply f
                                             [(ddtok,
                                                FStar_SMTEncoding_Term.Term_sort)] in
                                         let uu____14450 =
                                           let uu____14456 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14456) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14450
                                     | uu____14469 -> tok_typing in
                                   let uu____14474 =
                                     encode_binders
                                       (FStar_Pervasives_Native.Some fuel_tm)
                                       formals env1 in
                                   (match uu____14474 with
                                    | (vars',guards',env'',decls_formals,uu____14489)
                                        ->
                                        let uu____14496 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred
                                            (FStar_Pervasives_Native.Some
                                               fuel_tm) t_res env'' dapp1 in
                                        (match uu____14496 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14515 ->
                                                   let uu____14519 =
                                                     let uu____14520 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14520 in
                                                   [uu____14519] in
                                             let encode_elim uu____14527 =
                                               let uu____14528 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14528 with
                                               | (head1,args) ->
                                                   let uu____14557 =
                                                     let uu____14558 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14558.FStar_Syntax_Syntax.n in
                                                   (match uu____14557 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14565;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14566;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14567;_},uu____14568)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14578 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14578
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14604
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14612
                                                                    =
                                                                    let uu____14613
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14613 in
                                                                    if
                                                                    uu____14612
                                                                    then
                                                                    let uu____14620
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14620]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14622
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14635
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14635
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14657
                                                                    =
                                                                    let uu____14661
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14661 in
                                                                    (match uu____14657
                                                                    with
                                                                    | 
                                                                    (uu____14668,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14674
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14674
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14676
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14676
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 encoded_args in
                                                             (match uu____14622
                                                              with
                                                              | (uu____14684,arg_vars,elim_eqns_or_guards,uu____14687)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14706
                                                                    =
                                                                    let uu____14710
                                                                    =
                                                                    let uu____14711
                                                                    =
                                                                    let uu____14717
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14723
                                                                    =
                                                                    let uu____14724
                                                                    =
                                                                    let uu____14727
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14727) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14724 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14717,
                                                                    uu____14723) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14711 in
                                                                    (uu____14710,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14706 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14740
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14740,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14742
                                                                    =
                                                                    let uu____14746
                                                                    =
                                                                    let uu____14747
                                                                    =
                                                                    let uu____14753
                                                                    =
                                                                    let uu____14756
                                                                    =
                                                                    let uu____14758
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14758] in
                                                                    [uu____14756] in
                                                                    let uu____14761
                                                                    =
                                                                    let uu____14762
                                                                    =
                                                                    let uu____14765
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14766
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14765,
                                                                    uu____14766) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14762 in
                                                                    (uu____14753,
                                                                    [x],
                                                                    uu____14761) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14747 in
                                                                    let uu____14776
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14746,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____14776) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14742
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14781
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
                                                                    (let uu____14796
                                                                    =
                                                                    let uu____14797
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14797
                                                                    dapp1 in
                                                                    [uu____14796]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14781
                                                                    FStar_List.flatten in
                                                                    let uu____14801
                                                                    =
                                                                    let uu____14805
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    let uu____14812
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14818
                                                                    =
                                                                    let uu____14819
                                                                    =
                                                                    let uu____14822
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14822) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14819 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14812,
                                                                    uu____14818) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14806 in
                                                                    (uu____14805,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14801) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14838 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14838
                                                         with
                                                         | (encoded_args,arg_decls)
                                                             ->
                                                             let guards_for_parameter
                                                               arg xv =
                                                               let fv1 =
                                                                 match 
                                                                   arg.FStar_SMTEncoding_Term.tm
                                                                 with
                                                                 | FStar_SMTEncoding_Term.FreeV
                                                                    fv1 ->
                                                                    fv1
                                                                 | uu____14864
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14872
                                                                    =
                                                                    let uu____14873
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14873 in
                                                                    if
                                                                    uu____14872
                                                                    then
                                                                    let uu____14880
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14880]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14882
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14895
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14895
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14917
                                                                    =
                                                                    let uu____14921
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    FStar_Pervasives_Native.None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14921 in
                                                                    (match uu____14917
                                                                    with
                                                                    | 
                                                                    (uu____14928,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14934
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14934
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14936
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14936
                                                                    ::
                                                                    eqns_or_guards) in
                                                                    (env3,
                                                                    (xv ::
                                                                    arg_vars),
                                                                    eqns,
                                                                    (i +
                                                                    (Prims.parse_int
                                                                    "1")))))
                                                                 (env', [],
                                                                   [],
                                                                   (Prims.parse_int
                                                                    "0"))
                                                                 encoded_args in
                                                             (match uu____14882
                                                              with
                                                              | (uu____14944,arg_vars,elim_eqns_or_guards,uu____14947)
                                                                  ->
                                                                  let arg_vars1
                                                                    =
                                                                    FStar_List.rev
                                                                    arg_vars in
                                                                  let ty =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (encoded_head,
                                                                    arg_vars1) in
                                                                  let xvars1
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    vars in
                                                                  let dapp1 =
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    (ddconstrsym,
                                                                    xvars1) in
                                                                  let ty_pred
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                                    (FStar_Pervasives_Native.Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14966
                                                                    =
                                                                    let uu____14970
                                                                    =
                                                                    let uu____14971
                                                                    =
                                                                    let uu____14977
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14983
                                                                    =
                                                                    let uu____14984
                                                                    =
                                                                    let uu____14987
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14987) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14984 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14977,
                                                                    uu____14983) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14971 in
                                                                    (uu____14970,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14966 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Parser_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15000
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15000,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15002
                                                                    =
                                                                    let uu____15006
                                                                    =
                                                                    let uu____15007
                                                                    =
                                                                    let uu____15013
                                                                    =
                                                                    let uu____15016
                                                                    =
                                                                    let uu____15018
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15018] in
                                                                    [uu____15016] in
                                                                    let uu____15021
                                                                    =
                                                                    let uu____15022
                                                                    =
                                                                    let uu____15025
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15026
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15025,
                                                                    uu____15026) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15022 in
                                                                    (uu____15013,
                                                                    [x],
                                                                    uu____15021) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15007 in
                                                                    let uu____15036
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15006,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "lextop is top"),
                                                                    uu____15036) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15002
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15041
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
                                                                    (let uu____15056
                                                                    =
                                                                    let uu____15057
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15057
                                                                    dapp1 in
                                                                    [uu____15056]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15041
                                                                    FStar_List.flatten in
                                                                    let uu____15061
                                                                    =
                                                                    let uu____15065
                                                                    =
                                                                    let uu____15066
                                                                    =
                                                                    let uu____15072
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15078
                                                                    =
                                                                    let uu____15079
                                                                    =
                                                                    let uu____15082
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15082) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15079 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15072,
                                                                    uu____15078) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15066 in
                                                                    (uu____15065,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15061) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15092 ->
                                                        ((let uu____15094 =
                                                            let uu____15095 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15096 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15095
                                                              uu____15096 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15094);
                                                         ([], []))) in
                                             let uu____15099 = encode_elim () in
                                             (match uu____15099 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15111 =
                                                      let uu____15113 =
                                                        let uu____15115 =
                                                          let uu____15117 =
                                                            let uu____15119 =
                                                              let uu____15120
                                                                =
                                                                let uu____15126
                                                                  =
                                                                  let uu____15128
                                                                    =
                                                                    let uu____15129
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15129 in
                                                                  FStar_Pervasives_Native.Some
                                                                    uu____15128 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15126) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15120 in
                                                            [uu____15119] in
                                                          let uu____15132 =
                                                            let uu____15134 =
                                                              let uu____15136
                                                                =
                                                                let uu____15138
                                                                  =
                                                                  let uu____15140
                                                                    =
                                                                    let uu____15142
                                                                    =
                                                                    let uu____15144
                                                                    =
                                                                    let uu____15145
                                                                    =
                                                                    let uu____15149
                                                                    =
                                                                    let uu____15150
                                                                    =
                                                                    let uu____15156
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15156) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15150 in
                                                                    (uu____15149,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15145 in
                                                                    let uu____15163
                                                                    =
                                                                    let uu____15165
                                                                    =
                                                                    let uu____15166
                                                                    =
                                                                    let uu____15170
                                                                    =
                                                                    let uu____15171
                                                                    =
                                                                    let uu____15177
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15183
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15177,
                                                                    uu____15183) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15171 in
                                                                    (uu____15170,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15166 in
                                                                    [uu____15165] in
                                                                    uu____15144
                                                                    ::
                                                                    uu____15163 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (FStar_Pervasives_Native.Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15142 in
                                                                  FStar_List.append
                                                                    uu____15140
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15138 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15136 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15134 in
                                                          FStar_List.append
                                                            uu____15117
                                                            uu____15132 in
                                                        FStar_List.append
                                                          decls3 uu____15115 in
                                                      FStar_List.append
                                                        decls2 uu____15113 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15111 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____15204  ->
              fun se  ->
                match uu____15204 with
                | (g,env1) ->
                    let uu____15216 = encode_sigelt env1 se in
                    (match uu____15216 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t,env_t) FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15252 =
        match uu____15252 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15270 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15275 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15275
                   then
                     let uu____15276 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15277 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15278 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15276 uu____15277 uu____15278
                   else ());
                  (let uu____15280 = encode_term t1 env1 in
                   match uu____15280 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15290 =
                         let uu____15294 =
                           let uu____15295 =
                             let uu____15296 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15296
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15295 in
                         new_term_constant_from_string env1 x uu____15294 in
                       (match uu____15290 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                FStar_Pervasives_Native.None xx t in
                            let caption =
                              let uu____15307 = FStar_Options.log_queries () in
                              if uu____15307
                              then
                                let uu____15309 =
                                  let uu____15310 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15311 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15312 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15310 uu____15311 uu____15312 in
                                FStar_Pervasives_Native.Some uu____15309
                              else FStar_Pervasives_Native.None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (FStar_Pervasives_Native.Some a_name),
                                  a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15323,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant
                     FStar_Pervasives_Native.None in
                 let uu____15332 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15332 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15345,se,uu____15347) ->
                 let uu____15350 = encode_sigelt env1 se in
                 (match uu____15350 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15360,se) ->
                 let uu____15364 = encode_sigelt env1 se in
                 (match uu____15364 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15374 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15374 with | (uu____15386,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15431  ->
            match uu____15431 with
            | (l,uu____15438,uu____15439) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((FStar_Pervasives_Native.fst l), [],
                    FStar_SMTEncoding_Term.Bool_sort,
                    FStar_Pervasives_Native.None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15460  ->
            match uu____15460 with
            | (l,uu____15468,uu____15469) ->
                let uu____15474 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (FStar_Pervasives_Native.fst l) in
                let uu____15475 =
                  let uu____15477 =
                    let uu____15478 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15478 in
                  [uu____15477] in
                uu____15474 :: uu____15475)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15489 =
      let uu____15491 =
        let uu____15492 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15494 =
          let uu____15495 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15495 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15492;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15494
        } in
      [uu____15491] in
    FStar_ST.write last_env uu____15489
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15505 = FStar_ST.read last_env in
      match uu____15505 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15511 ->
          let uu___154_15513 = e in
          let uu____15514 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15513.bindings);
            depth = (uu___154_15513.depth);
            tcenv;
            warn = (uu___154_15513.warn);
            cache = (uu___154_15513.cache);
            nolabels = (uu___154_15513.nolabels);
            use_zfuel_name = (uu___154_15513.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15513.encode_non_total_function_typ);
            current_module_name = uu____15514
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15518 = FStar_ST.read last_env in
    match uu____15518 with
    | [] -> failwith "Empty env stack"
    | uu____15523::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15531  ->
    let uu____15532 = FStar_ST.read last_env in
    match uu____15532 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15543 = hd1 in
          {
            bindings = (uu___155_15543.bindings);
            depth = (uu___155_15543.depth);
            tcenv = (uu___155_15543.tcenv);
            warn = (uu___155_15543.warn);
            cache = refs;
            nolabels = (uu___155_15543.nolabels);
            use_zfuel_name = (uu___155_15543.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15543.encode_non_total_function_typ);
            current_module_name = (uu___155_15543.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15549  ->
    let uu____15550 = FStar_ST.read last_env in
    match uu____15550 with
    | [] -> failwith "Popping an empty stack"
    | uu____15555::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15563  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15566  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15569  ->
    let uu____15570 = FStar_ST.read last_env in
    match uu____15570 with
    | hd1::uu____15576::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15582 -> failwith "Impossible"
let init: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    init_env tcenv;
    FStar_SMTEncoding_Z3.init ();
    FStar_SMTEncoding_Z3.giveZ3 [FStar_SMTEncoding_Term.DefPrelude]
let push: Prims.string -> Prims.unit =
  fun msg  -> push_env (); varops.push (); FStar_SMTEncoding_Z3.push msg
let pop: Prims.string -> Prims.unit =
  fun msg  -> pop_env (); varops.pop (); FStar_SMTEncoding_Z3.pop msg
let mark: Prims.string -> Prims.unit =
  fun msg  -> mark_env (); varops.mark (); FStar_SMTEncoding_Z3.mark msg
let reset_mark: Prims.string -> Prims.unit =
  fun msg  ->
    reset_mark_env ();
    varops.reset_mark ();
    FStar_SMTEncoding_Z3.reset_mark msg
let commit_mark: Prims.string -> Prims.unit =
  fun msg  ->
    commit_mark_env ();
    varops.commit_mark ();
    FStar_SMTEncoding_Z3.commit_mark msg
let open_fact_db_tags: env_t -> FStar_SMTEncoding_Term.fact_db_id Prims.list
  = fun env  -> []
let place_decl_in_fact_dbs:
  env_t ->
    FStar_SMTEncoding_Term.fact_db_id Prims.list ->
      FStar_SMTEncoding_Term.decl -> FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun fact_db_ids  ->
      fun d  ->
        match (fact_db_ids, d) with
        | (uu____15631::uu____15632,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15636 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15636.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15636.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15636.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15637 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15648 =
        let uu____15650 =
          let uu____15651 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15651 in
        let uu____15652 = open_fact_db_tags env in uu____15650 :: uu____15652 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15648
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list,env_t)
        FStar_Pervasives_Native.tuple2
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____15667 = encode_sigelt env se in
      match uu____15667 with
      | (g,env1) ->
          let g1 =
            FStar_All.pipe_right g
              (FStar_List.map (place_decl_in_fact_dbs env1 fact_db_ids)) in
          (g1, env1)
let encode_sig:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.sigelt -> Prims.unit =
  fun tcenv  ->
    fun se  ->
      let caption decls =
        let uu____15692 = FStar_Options.log_queries () in
        if uu____15692
        then
          let uu____15694 =
            let uu____15695 =
              let uu____15696 =
                let uu____15697 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15697 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15696 in
            FStar_SMTEncoding_Term.Caption uu____15695 in
          uu____15694 :: decls
        else decls in
      let env =
        let uu____15704 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15704 tcenv in
      let uu____15705 = encode_top_level_facts env se in
      match uu____15705 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15714 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15714))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15725 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15725
       then
         let uu____15726 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15726
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15747  ->
                 fun se  ->
                   match uu____15747 with
                   | (g,env2) ->
                       let uu____15759 = encode_top_level_facts env2 se in
                       (match uu____15759 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15772 =
         encode_signature
           (let uu___157_15776 = env in
            {
              bindings = (uu___157_15776.bindings);
              depth = (uu___157_15776.depth);
              tcenv = (uu___157_15776.tcenv);
              warn = false;
              cache = (uu___157_15776.cache);
              nolabels = (uu___157_15776.nolabels);
              use_zfuel_name = (uu___157_15776.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15776.encode_non_total_function_typ);
              current_module_name = (uu___157_15776.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15772 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15788 = FStar_Options.log_queries () in
             if uu____15788
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15793 = env1 in
               {
                 bindings = (uu___158_15793.bindings);
                 depth = (uu___158_15793.depth);
                 tcenv = (uu___158_15793.tcenv);
                 warn = true;
                 cache = (uu___158_15793.cache);
                 nolabels = (uu___158_15793.nolabels);
                 use_zfuel_name = (uu___158_15793.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15793.encode_non_total_function_typ);
                 current_module_name = (uu___158_15793.current_module_name)
               });
            (let uu____15795 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15795
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
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
        (let uu____15830 =
           let uu____15831 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15831.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15830);
        (let env =
           let uu____15833 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15833 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15840 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15861 = aux rest in
                 (match uu____15861 with
                  | (out,rest1) ->
                      let t =
                        let uu____15879 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15879 with
                        | FStar_Pervasives_Native.Some uu____15883 ->
                            let uu____15884 =
                              FStar_Syntax_Syntax.new_bv
                                FStar_Pervasives_Native.None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15884
                              x.FStar_Syntax_Syntax.sort
                        | uu____15885 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15888 =
                        let uu____15890 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_15891 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_15891.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_15891.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15890 :: out in
                      (uu____15888, rest1))
             | uu____15894 -> ([], bindings1) in
           let uu____15898 = aux bindings in
           match uu____15898 with
           | (closing,bindings1) ->
               let uu____15912 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15912, bindings1) in
         match uu____15840 with
         | (q1,bindings1) ->
             let uu____15925 =
               let uu____15928 =
                 FStar_List.filter
                   (fun uu___125_15930  ->
                      match uu___125_15930 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15931 ->
                          false
                      | uu____15935 -> true) bindings1 in
               encode_env_bindings env uu____15928 in
             (match uu____15925 with
              | (env_decls,env1) ->
                  ((let uu____15946 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15946
                    then
                      let uu____15947 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15947
                    else ());
                   (let uu____15949 = encode_formula q1 env1 in
                    match uu____15949 with
                    | (phi,qdecls) ->
                        let uu____15961 =
                          let uu____15964 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15964 phi in
                        (match uu____15961 with
                         | (labels,phi1) ->
                             let uu____15974 = encode_labels labels in
                             (match uu____15974 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15995 =
                                      let uu____15999 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16000 =
                                        varops.mk_unique "@query" in
                                      (uu____15999,
                                        (FStar_Pervasives_Native.Some "query"),
                                        uu____16000) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15995 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16013 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16013 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16015 = encode_formula q env in
       match uu____16015 with
       | (f,uu____16019) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16021) -> true
             | uu____16024 -> false)))