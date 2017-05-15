open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___104_74  ->
       match uu___104_74 with
       | (FStar_Util.Inl uu____79,uu____80) -> false
       | uu____83 -> true) args
let subst_lcomp_opt s l =
  match l with
  | Some (FStar_Util.Inl l1) ->
      let uu____114 =
        let uu____117 =
          let uu____118 =
            let uu____121 = l1.FStar_Syntax_Syntax.comp () in
            FStar_Syntax_Subst.subst_comp s uu____121 in
          FStar_All.pipe_left FStar_Syntax_Util.lcomp_of_comp uu____118 in
        FStar_Util.Inl uu____117 in
      Some uu____114
  | uu____126 -> l
let escape: Prims.string -> Prims.string =
  fun s  -> FStar_Util.replace_char s '\'' '_'
let mk_term_projector_name:
  FStar_Ident.lident -> FStar_Syntax_Syntax.bv -> Prims.string =
  fun lid  ->
    fun a  ->
      let a1 =
        let uu___129_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___129_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___129_140.FStar_Syntax_Syntax.sort)
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
                         mk_term_projector_name lid (Prims.fst b)))
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
      | None  -> y1
      | Some uu____486 ->
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
      FStar_All.pipe_left Prims.fst uu____498 in
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
    | Some f -> f
    | None  ->
        let id = next_id1 () in
        let f =
          let uu____593 = FStar_SMTEncoding_Util.mk_String_const id in
          FStar_All.pipe_left FStar_SMTEncoding_Term.boxString uu____593 in
        let top_scope =
          let uu____596 =
            let uu____601 = FStar_ST.read scopes in FStar_List.hd uu____601 in
          FStar_All.pipe_left Prims.snd uu____596 in
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
    let uu___130_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___130_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___130_780.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option*
  (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term) Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____805 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____831 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term
      Prims.option*
      (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
      Prims.option)
  = fun projectee  -> match projectee with | Binding_fvar _0 -> _0
let binder_of_eithervar v1 = (v1, None)
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
  use_fuel_instrumented_version: FStar_SMTEncoding_Term.term Prims.option;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___105_1015  ->
            match uu___105_1015 with
            | FStar_SMTEncoding_Term.Assume a ->
                [a.FStar_SMTEncoding_Term.assumption_name]
            | uu____1018 -> [])) in
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
    let uu____1026 =
      FStar_All.pipe_right e.bindings
        (FStar_List.map
           (fun uu___106_1030  ->
              match uu___106_1030 with
              | Binding_var (x,uu____1032) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1034,uu____1035,uu____1036) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1026 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____1073 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1073
      then
        let uu____1075 = FStar_Syntax_Print.term_to_string t in
        Some uu____1075
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1086 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1086)
let gen_term_var:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym = Prims.strcat "@x" (Prims.string_of_int env.depth) in
      let y =
        FStar_SMTEncoding_Util.mkFreeV
          (ysym, FStar_SMTEncoding_Term.Term_sort) in
      (ysym, y,
        (let uu___131_1098 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___131_1098.tcenv);
           warn = (uu___131_1098.warn);
           cache = (uu___131_1098.cache);
           nolabels = (uu___131_1098.nolabels);
           use_fuel_instrumented_version =
             (uu___131_1098.use_fuel_instrumented_version);
           encode_non_total_function_typ =
             (uu___131_1098.encode_non_total_function_typ);
           current_module_name = (uu___131_1098.current_module_name)
         }))
let new_term_constant:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      let ysym =
        varops.new_var x.FStar_Syntax_Syntax.ppname
          x.FStar_Syntax_Syntax.index in
      let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
      (ysym, y,
        (let uu___132_1111 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___132_1111.depth);
           tcenv = (uu___132_1111.tcenv);
           warn = (uu___132_1111.warn);
           cache = (uu___132_1111.cache);
           nolabels = (uu___132_1111.nolabels);
           use_fuel_instrumented_version =
             (uu___132_1111.use_fuel_instrumented_version);
           encode_non_total_function_typ =
             (uu___132_1111.encode_non_total_function_typ);
           current_module_name = (uu___132_1111.current_module_name)
         }))
let new_term_constant_from_string:
  env_t ->
    FStar_Syntax_Syntax.bv ->
      Prims.string -> (Prims.string* FStar_SMTEncoding_Term.term* env_t)
  =
  fun env  ->
    fun x  ->
      fun str  ->
        let ysym = varops.mk_unique str in
        let y = FStar_SMTEncoding_Util.mkApp (ysym, []) in
        (ysym, y,
          (let uu___133_1127 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___133_1127.depth);
             tcenv = (uu___133_1127.tcenv);
             warn = (uu___133_1127.warn);
             cache = (uu___133_1127.cache);
             nolabels = (uu___133_1127.nolabels);
             use_fuel_instrumented_version =
               (uu___133_1127.use_fuel_instrumented_version);
             encode_non_total_function_typ =
               (uu___133_1127.encode_non_total_function_typ);
             current_module_name = (uu___133_1127.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___134_1137 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___134_1137.depth);
          tcenv = (uu___134_1137.tcenv);
          warn = (uu___134_1137.warn);
          cache = (uu___134_1137.cache);
          nolabels = (uu___134_1137.nolabels);
          use_fuel_instrumented_version =
            (uu___134_1137.use_fuel_instrumented_version);
          encode_non_total_function_typ =
            (uu___134_1137.encode_non_total_function_typ);
          current_module_name = (uu___134_1137.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___107_1153  ->
             match uu___107_1153 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1161 -> None) in
      let uu____1164 = aux a in
      match uu____1164 with
      | None  ->
          let a2 = unmangle a in
          let uu____1171 = aux a2 in
          (match uu____1171 with
           | None  ->
               let uu____1177 =
                 let uu____1178 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1179 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1178 uu____1179 in
               failwith uu____1177
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1199 =
        let uu___135_1200 = env in
        let uu____1201 =
          let uu____1203 =
            let uu____1204 =
              let uu____1213 =
                let uu____1215 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1215 in
              (x, fname, uu____1213, None) in
            Binding_fvar uu____1204 in
          uu____1203 :: (env.bindings) in
        {
          bindings = uu____1201;
          depth = (uu___135_1200.depth);
          tcenv = (uu___135_1200.tcenv);
          warn = (uu___135_1200.warn);
          cache = (uu___135_1200.cache);
          nolabels = (uu___135_1200.nolabels);
          use_fuel_instrumented_version =
            (uu___135_1200.use_fuel_instrumented_version);
          encode_non_total_function_typ =
            (uu___135_1200.encode_non_total_function_typ);
          current_module_name = (uu___135_1200.current_module_name)
        } in
      (fname, ftok, uu____1199)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
        Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___108_1245  ->
           match uu___108_1245 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1277 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1291 =
        lookup_binding env
          (fun uu___109_1293  ->
             match uu___109_1293 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1307 -> None) in
      FStar_All.pipe_right uu____1291 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        (FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term)
        Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1322 = try_lookup_lid env a in
      match uu____1322 with
      | None  ->
          let uu____1345 =
            let uu____1346 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1346 in
          failwith uu____1345
      | Some s -> s
let push_free_var:
  env_t ->
    FStar_Ident.lident ->
      Prims.string -> FStar_SMTEncoding_Term.term Prims.option -> env_t
  =
  fun env  ->
    fun x  ->
      fun fname  ->
        fun ftok  ->
          let uu___136_1383 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___136_1383.depth);
            tcenv = (uu___136_1383.tcenv);
            warn = (uu___136_1383.warn);
            cache = (uu___136_1383.cache);
            nolabels = (uu___136_1383.nolabels);
            use_fuel_instrumented_version =
              (uu___136_1383.use_fuel_instrumented_version);
            encode_non_total_function_typ =
              (uu___136_1383.encode_non_total_function_typ);
            current_module_name = (uu___136_1383.current_module_name)
          }
let push_zfuel_name: env_t -> FStar_Ident.lident -> Prims.string -> env_t =
  fun env  ->
    fun x  ->
      fun f  ->
        let uu____1399 = lookup_lid env x in
        match uu____1399 with
        | (t1,t2,uu____1409) ->
            let t3 n1 = FStar_SMTEncoding_Util.mkApp (f, [n1]) in
            let uu___137_1423 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___137_1423.depth);
              tcenv = (uu___137_1423.tcenv);
              warn = (uu___137_1423.warn);
              cache = (uu___137_1423.cache);
              nolabels = (uu___137_1423.nolabels);
              use_fuel_instrumented_version =
                (uu___137_1423.use_fuel_instrumented_version);
              encode_non_total_function_typ =
                (uu___137_1423.encode_non_total_function_typ);
              current_module_name = (uu___137_1423.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1437 = try_lookup_lid env l in
      match uu____1437 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match (zf_opt, (env.use_fuel_instrumented_version)) with
           | (Some f,Some fuel) -> let uu____1487 = f fuel in Some uu____1487
           | uu____1488 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1498,fuel::[]) ->
                         let uu____1501 =
                           let uu____1502 =
                             let uu____1503 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1503 Prims.fst in
                           FStar_Util.starts_with uu____1502 "fuel" in
                         if uu____1501
                         then
                           let uu____1505 =
                             let uu____1506 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1506
                               fuel in
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                             uu____1505
                         else Some t
                     | uu____1509 -> Some t)
                | uu____1510 -> None))
let lookup_free_var env a =
  let uu____1528 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1528 with
  | Some t -> t
  | None  ->
      let uu____1531 =
        let uu____1532 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1532 in
      failwith uu____1531
let lookup_free_var_name env a =
  let uu____1549 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1549 with | (x,uu____1558,uu____1559) -> x
let lookup_free_var_sym env a =
  let uu____1587 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1587 with
  | (name,sym,zf_opt) ->
      (match (zf_opt, (env.use_fuel_instrumented_version)) with
       | (Some mkf,Some fuel) ->
           let uu____1626 =
             let uu____1627 = mkf fuel in
             uu____1627.FStar_SMTEncoding_Term.tm in
           (match uu____1626 with
            | FStar_SMTEncoding_Term.App (g,zf) -> (g, zf)
            | uu____1636 -> failwith "Impossible")
       | uu____1640 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1659 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___110_1668  ->
           match uu___110_1668 with
           | Binding_fvar (uu____1670,nm',tok,uu____1673) when nm = nm' ->
               tok
           | uu____1682 -> None)
let mkForall_fuel' n1 uu____1699 =
  match uu____1699 with
  | (pats,vars,body) ->
      let fallback uu____1715 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1718 = FStar_Options.unthrottle_inductives () in
      if uu____1718
      then fallback ()
      else
        (let uu____1720 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1720 with
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
                       | uu____1739 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1753 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1753
                     | uu____1755 ->
                         let uu____1756 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1756 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1759 -> body in
             let vars1 = (fsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars in
             FStar_SMTEncoding_Util.mkForall (pats1, vars1, body1))
let mkForall_fuel:
  (FStar_SMTEncoding_Term.pat Prims.list Prims.list*
    FStar_SMTEncoding_Term.fvs* FStar_SMTEncoding_Term.term) ->
    FStar_SMTEncoding_Term.term
  = mkForall_fuel' (Prims.parse_int "1")
let head_normal: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let t1 = FStar_Syntax_Util.unmeta t in
      match t1.FStar_Syntax_Syntax.n with
      | FStar_Syntax_Syntax.Tm_arrow _
        |FStar_Syntax_Syntax.Tm_refine _
         |FStar_Syntax_Syntax.Tm_bvar _
          |FStar_Syntax_Syntax.Tm_uvar _
           |FStar_Syntax_Syntax.Tm_abs _|FStar_Syntax_Syntax.Tm_constant _
          -> true
      | FStar_Syntax_Syntax.Tm_fvar fv|FStar_Syntax_Syntax.Tm_app
        ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
           FStar_Syntax_Syntax.tk = _; FStar_Syntax_Syntax.pos = _;
           FStar_Syntax_Syntax.vars = _;_},_)
          ->
          let uu____1803 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1803 FStar_Option.isNone
      | uu____1816 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1823 =
        let uu____1824 = FStar_Syntax_Util.un_uinst t in
        uu____1824.FStar_Syntax_Syntax.n in
      match uu____1823 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1827,uu____1828,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___111_1857  ->
                  match uu___111_1857 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1858 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1859,uu____1860,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1887 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1887 FStar_Option.isSome
      | uu____1900 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1907 = head_normal env t in
      if uu____1907
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
    let uu____1918 =
      let uu____1919 = FStar_Syntax_Syntax.null_binder t in [uu____1919] in
    let uu____1920 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1918 uu____1920 None
let mk_Apply:
  FStar_SMTEncoding_Term.term ->
    (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
      FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun vars  ->
      FStar_All.pipe_right vars
        (FStar_List.fold_left
           (fun out  ->
              fun var  ->
                match Prims.snd var with
                | FStar_SMTEncoding_Term.Fuel_sort  ->
                    let uu____1947 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1947
                | s ->
                    let uu____1950 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1950) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___112_1962  ->
    match uu___112_1962 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1963 -> false
let is_an_eta_expansion:
  env_t ->
    FStar_SMTEncoding_Term.fv Prims.list ->
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term Prims.option
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
                       FStar_SMTEncoding_Term.freevars = uu____1991;
                       FStar_SMTEncoding_Term.rng = uu____1992;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2006) ->
              let uu____2011 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2021 -> false) args (FStar_List.rev xs)) in
              if uu____2011 then tok_of_name env f else None
          | (uu____2024,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2027 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2029 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2029)) in
              if uu____2027 then Some t else None
          | uu____2032 -> None in
        check_partial_applications body (FStar_List.rev vars)
type label = (FStar_SMTEncoding_Term.fv* Prims.string* FStar_Range.range)
type labels = label Prims.list
type pattern =
  {
  pat_vars: (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.fv) Prims.list;
  pat_term:
    Prims.unit ->
      (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t);
  guard: FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term;
  projections:
    FStar_SMTEncoding_Term.term ->
      (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) Prims.list;}
exception Let_rec_unencodeable
let uu___is_Let_rec_unencodeable: Prims.exn -> Prims.bool =
  fun projectee  ->
    match projectee with
    | Let_rec_unencodeable  -> true
    | uu____2116 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___113_2119  ->
    match uu___113_2119 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2121 =
          let uu____2125 =
            let uu____2127 =
              let uu____2128 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2128 in
            [uu____2127] in
          ("FStar.Char.Char", uu____2125) in
        FStar_SMTEncoding_Util.mkApp uu____2121
    | FStar_Const.Const_int (i,None ) ->
        let uu____2136 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2136
    | FStar_Const.Const_int (i,Some uu____2138) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2147) ->
        let uu____2150 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2150
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2154 =
          let uu____2155 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2155 in
        failwith uu____2154
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2174 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2182 ->
            let uu____2187 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2187
        | uu____2188 ->
            if norm1
            then let uu____2189 = whnf env t1 in aux false uu____2189
            else
              (let uu____2191 =
                 let uu____2192 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2193 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2192 uu____2193 in
               failwith uu____2191) in
      aux true t0
let curried_arrow_formals_comp:
  FStar_Syntax_Syntax.term ->
    (FStar_Syntax_Syntax.binders* FStar_Syntax_Syntax.comp)
  =
  fun k  ->
    let k1 = FStar_Syntax_Subst.compress k in
    match k1.FStar_Syntax_Syntax.n with
    | FStar_Syntax_Syntax.Tm_arrow (bs,c) ->
        FStar_Syntax_Subst.open_comp bs c
    | uu____2214 ->
        let uu____2215 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2215)
let rec encode_binders:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.binders ->
      env_t ->
        (FStar_SMTEncoding_Term.fv Prims.list* FStar_SMTEncoding_Term.term
          Prims.list* env_t* FStar_SMTEncoding_Term.decls_t*
          FStar_Syntax_Syntax.bv Prims.list)
  =
  fun fuel_opt  ->
    fun bs  ->
      fun env  ->
        (let uu____2355 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2355
         then
           let uu____2356 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2356
         else ());
        (let uu____2358 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2394  ->
                   fun b  ->
                     match uu____2394 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2437 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2446 = gen_term_var env1 x in
                           match uu____2446 with
                           | (xxsym,xx,env') ->
                               let uu____2460 =
                                 let uu____2463 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2463 env1 xx in
                               (match uu____2460 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2437 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2358 with
         | (vars,guards,env1,decls,names1) ->
             ((FStar_List.rev vars), (FStar_List.rev guards), env1, decls,
               (FStar_List.rev names1)))
and encode_term_pred:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2551 = encode_term t env in
          match uu____2551 with
          | (t1,decls) ->
              let uu____2558 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2558, decls)
and encode_term_pred':
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t ->
        FStar_SMTEncoding_Term.term ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun fuel_opt  ->
    fun t  ->
      fun env  ->
        fun e  ->
          let uu____2566 = encode_term t env in
          match uu____2566 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2575 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2575, decls)
               | Some f ->
                   let uu____2577 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2577, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2584 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2584
       then
         let uu____2585 = FStar_Syntax_Print.tag_of_term t in
         let uu____2586 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2587 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2585 uu____2586
           uu____2587
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2592 =
             let uu____2593 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2594 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2595 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2596 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2593
               uu____2594 uu____2595 uu____2596 in
           failwith uu____2592
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2600 =
             let uu____2601 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2601 in
           failwith uu____2600
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2606) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2636) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2645 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2645, [])
       | FStar_Syntax_Syntax.Tm_type uu____2651 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2654) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2660 = encode_const c in (uu____2660, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2675 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2675 with
            | (binders1,res) ->
                let uu____2682 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2682
                then
                  let uu____2685 = encode_binders None binders1 env in
                  (match uu____2685 with
                   | (vars,guards,env',decls,uu____2700) ->
                       let fsym =
                         let uu____2710 = varops.fresh "f" in
                         (uu____2710, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2713 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___138_2717 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___138_2717.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___138_2717.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___138_2717.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___138_2717.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___138_2717.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___138_2717.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___138_2717.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___138_2717.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___138_2717.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___138_2717.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___138_2717.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___138_2717.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___138_2717.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___138_2717.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___138_2717.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___138_2717.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___138_2717.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___138_2717.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___138_2717.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___138_2717.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___138_2717.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___138_2717.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___138_2717.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2713 with
                        | (pre_opt,res_t) ->
                            let uu____2724 =
                              encode_term_pred None res_t env' app in
                            (match uu____2724 with
                             | (res_pred,decls') ->
                                 let uu____2731 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2738 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2738, [])
                                   | Some pre ->
                                       let uu____2741 =
                                         encode_formula pre env' in
                                       (match uu____2741 with
                                        | (guard,decls0) ->
                                            let uu____2749 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2749, decls0)) in
                                 (match uu____2731 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2757 =
                                          let uu____2763 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2763) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2757 in
                                      let cvars =
                                        let uu____2773 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2773
                                          (FStar_List.filter
                                             (fun uu____2779  ->
                                                match uu____2779 with
                                                | (x,uu____2783) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2794 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2794 with
                                       | Some cache_entry ->
                                           let uu____2799 =
                                             let uu____2800 =
                                               let uu____2804 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2804) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2800 in
                                           (uu____2799,
                                             (use_cache_entry cache_entry))
                                       | None  ->
                                           let tsym =
                                             let uu____2815 =
                                               let uu____2816 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2816 in
                                             varops.mk_unique uu____2815 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2823 =
                                               FStar_Options.log_queries () in
                                             if uu____2823
                                             then
                                               let uu____2825 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2825
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2831 =
                                               let uu____2835 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2835) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2831 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2843 =
                                               let uu____2847 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2847, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2843 in
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
                                             let uu____2860 =
                                               let uu____2864 =
                                                 let uu____2865 =
                                                   let uu____2871 =
                                                     let uu____2872 =
                                                       let uu____2875 =
                                                         let uu____2876 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2876 in
                                                       (f_has_t, uu____2875) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2872 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2871) in
                                                 mkForall_fuel uu____2865 in
                                               (uu____2864,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2860 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2889 =
                                               let uu____2893 =
                                                 let uu____2894 =
                                                   let uu____2900 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2900) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2894 in
                                               (uu____2893, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2889 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2914 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2914);
                                            (t1, t_decls)))))))
                else
                  (let tsym = varops.fresh "Non_total_Tm_arrow" in
                   let tdecl =
                     FStar_SMTEncoding_Term.DeclFun
                       (tsym, [], FStar_SMTEncoding_Term.Term_sort, None) in
                   let t1 = FStar_SMTEncoding_Util.mkApp (tsym, []) in
                   let t_kinding =
                     let a_name =
                       Prims.strcat "non_total_function_typing_" tsym in
                     let uu____2925 =
                       let uu____2929 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2929, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2925 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2938 =
                       let uu____2942 =
                         let uu____2943 =
                           let uu____2949 =
                             let uu____2950 =
                               let uu____2953 =
                                 let uu____2954 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2954 in
                               (f_has_t, uu____2953) in
                             FStar_SMTEncoding_Util.mkImp uu____2950 in
                           ([[f_has_t]], [fsym], uu____2949) in
                         mkForall_fuel uu____2943 in
                       (uu____2942, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2938 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2968 ->
           let uu____2973 =
             let uu____2976 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2976 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2981;
                 FStar_Syntax_Syntax.pos = uu____2982;
                 FStar_Syntax_Syntax.vars = uu____2983;_} ->
                 let uu____2990 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2990 with
                  | (b,f1) ->
                      let uu____3004 =
                        let uu____3005 = FStar_List.hd b in
                        Prims.fst uu____3005 in
                      (uu____3004, f1))
             | uu____3010 -> failwith "impossible" in
           (match uu____2973 with
            | (x,f) ->
                let uu____3017 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3017 with
                 | (base_t,decls) ->
                     let uu____3024 = gen_term_var env x in
                     (match uu____3024 with
                      | (x1,xtm,env') ->
                          let uu____3033 = encode_formula f env' in
                          (match uu____3033 with
                           | (refinement,decls') ->
                               let uu____3040 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3040 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3051 =
                                        let uu____3053 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3057 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3053
                                          uu____3057 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3051 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3073  ->
                                              match uu____3073 with
                                              | (y,uu____3077) ->
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
                                    let uu____3096 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3096 with
                                     | Some cache_entry ->
                                         let uu____3101 =
                                           let uu____3102 =
                                             let uu____3106 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3106) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3102 in
                                         (uu____3101,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3118 =
                                             let uu____3119 =
                                               let uu____3120 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3120 in
                                             Prims.strcat module_name
                                               uu____3119 in
                                           varops.mk_unique uu____3118 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3129 =
                                             let uu____3133 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3133) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3129 in
                                         let x_has_t =
                                           FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                             (Some fterm) xtm t1 in
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
                                           let uu____3143 =
                                             let uu____3147 =
                                               let uu____3148 =
                                                 let uu____3154 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3154) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3148 in
                                             (uu____3147,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3143 in
                                         let t_kinding =
                                           let uu____3164 =
                                             let uu____3168 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3168,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3164 in
                                         let t_interp =
                                           let uu____3178 =
                                             let uu____3182 =
                                               let uu____3183 =
                                                 let uu____3189 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3189) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3183 in
                                             let uu____3201 =
                                               let uu____3203 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3203 in
                                             (uu____3182, uu____3201,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3178 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3208 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3208);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3225 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3225 in
           let uu____3229 = encode_term_pred None k env ttm in
           (match uu____3229 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3237 =
                    let uu____3241 =
                      let uu____3242 =
                        let uu____3243 =
                          let uu____3244 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3244 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3243 in
                      varops.mk_unique uu____3242 in
                    (t_has_k, (Some "Uvar typing"), uu____3241) in
                  FStar_SMTEncoding_Util.mkAssume uu____3237 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3250 ->
           let uu____3260 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3260 with
            | (head1,args_e) ->
                let uu____3288 =
                  let uu____3296 =
                    let uu____3297 = FStar_Syntax_Subst.compress head1 in
                    uu____3297.FStar_Syntax_Syntax.n in
                  (uu____3296, args_e) in
                (match uu____3288 with
                 | (uu____3307,uu____3308) when head_redex env head1 ->
                     let uu____3319 = whnf env t in
                     encode_term uu____3319 env
                 | (FStar_Syntax_Syntax.Tm_uinst
                    ({
                       FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
                       FStar_Syntax_Syntax.tk = _;
                       FStar_Syntax_Syntax.pos = _;
                       FStar_Syntax_Syntax.vars = _;_},_),_::(v1,_)::
                    (v2,_)::[])
                   |(FStar_Syntax_Syntax.Tm_fvar fv,_::(v1,_)::(v2,_)::[])
                     when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.lexcons_lid
                     ->
                     let uu____3393 = encode_term v1 env in
                     (match uu____3393 with
                      | (v11,decls1) ->
                          let uu____3400 = encode_term v2 env in
                          (match uu____3400 with
                           | (v21,decls2) ->
                               let uu____3407 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3407,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3409) ->
                     let e0 =
                       let uu____3421 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3421 in
                     ((let uu____3427 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3427
                       then
                         let uu____3428 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3428
                       else ());
                      (let e =
                         let uu____3433 =
                           let uu____3434 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3435 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3434
                             uu____3435 in
                         uu____3433 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3444),(arg,uu____3446)::[]) -> encode_term arg env
                 | uu____3464 ->
                     let uu____3472 = encode_args args_e env in
                     (match uu____3472 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3505 = encode_term head1 env in
                            match uu____3505 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3544 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3544 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3586  ->
                                                 fun uu____3587  ->
                                                   match (uu____3586,
                                                           uu____3587)
                                                   with
                                                   | ((bv,uu____3601),
                                                      (a,uu____3603)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3617 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3617
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3622 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3622 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3632 =
                                                   let uu____3636 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3641 =
                                                     let uu____3642 =
                                                       let uu____3643 =
                                                         let uu____3644 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3644 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3643 in
                                                     varops.mk_unique
                                                       uu____3642 in
                                                   (uu____3636,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3641) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3632 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3661 = lookup_free_var_sym env fv in
                            match uu____3661 with
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
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_uinst
                              ({
                                 FStar_Syntax_Syntax.n =
                                   FStar_Syntax_Syntax.Tm_fvar fv;
                                 FStar_Syntax_Syntax.tk = _;
                                 FStar_Syntax_Syntax.pos = _;
                                 FStar_Syntax_Syntax.vars = _;_},_)
                              |FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____3699 =
                                  let uu____3700 =
                                    let uu____3703 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3703 Prims.fst in
                                  FStar_All.pipe_right uu____3700 Prims.snd in
                                Some uu____3699
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3722,(FStar_Util.Inl t1,uu____3724),uu____3725)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3763,(FStar_Util.Inr c,uu____3765),uu____3766)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3804 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3824 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3824 in
                               let uu____3825 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3825 with
                                | (formals,c) ->
                                    (match head2.FStar_Syntax_Syntax.n with
                                     | FStar_Syntax_Syntax.Tm_uinst
                                       ({
                                          FStar_Syntax_Syntax.n =
                                            FStar_Syntax_Syntax.Tm_fvar fv;
                                          FStar_Syntax_Syntax.tk = _;
                                          FStar_Syntax_Syntax.pos = _;
                                          FStar_Syntax_Syntax.vars = _;_},_)
                                       |FStar_Syntax_Syntax.Tm_fvar fv when
                                         (FStar_List.length formals) =
                                           (FStar_List.length args)
                                         ->
                                         encode_full_app
                                           fv.FStar_Syntax_Syntax.fv_name
                                     | uu____3850 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3895 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3895 with
            | (bs1,body1,opening) ->
                let fallback uu____3910 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3915 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3915, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3926 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3926
                  | FStar_Util.Inr (eff,uu____3928) ->
                      let uu____3934 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3934 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3979 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___139_3980 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___139_3980.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___139_3980.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___139_3980.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___139_3980.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___139_3980.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___139_3980.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___139_3980.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___139_3980.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___139_3980.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___139_3980.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___139_3980.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___139_3980.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___139_3980.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___139_3980.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___139_3980.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___139_3980.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___139_3980.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___139_3980.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___139_3980.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___139_3980.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___139_3980.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___139_3980.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___139_3980.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____3979 FStar_Syntax_Syntax.U_unknown in
                        let uu____3981 =
                          let uu____3982 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3982 in
                        FStar_Util.Inl uu____3981
                    | FStar_Util.Inr (eff_name,uu____3989) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4020 =
                        let uu____4021 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4021 in
                      FStar_All.pipe_right uu____4020
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4033 =
                        let uu____4034 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4034 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4042 =
                          let uu____4043 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4043 in
                        FStar_All.pipe_right uu____4042
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4047 =
                             let uu____4048 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4048 in
                           FStar_All.pipe_right uu____4047
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4059 =
                         let uu____4060 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4060 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4059);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4075 =
                       (is_impure lc1) &&
                         (let uu____4076 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4076) in
                     if uu____4075
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4081 = encode_binders None bs1 env in
                        match uu____4081 with
                        | (vars,guards,envbody,decls,uu____4096) ->
                            let uu____4103 =
                              let uu____4111 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4111
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4103 with
                             | (lc2,body2) ->
                                 let uu____4136 = encode_term body2 envbody in
                                 (match uu____4136 with
                                  | (body3,decls') ->
                                      let uu____4143 =
                                        let uu____4148 = codomain_eff lc2 in
                                        match uu____4148 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4160 =
                                              encode_term tfun env in
                                            (match uu____4160 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4143 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4179 =
                                               let uu____4185 =
                                                 let uu____4186 =
                                                   let uu____4189 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4189, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4186 in
                                               ([], vars, uu____4185) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4179 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4197 =
                                                   let uu____4199 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4199 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4197 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4210 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4210 with
                                            | Some cache_entry ->
                                                let uu____4215 =
                                                  let uu____4216 =
                                                    let uu____4220 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4220) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4216 in
                                                (uu____4215,
                                                  (use_cache_entry
                                                     cache_entry))
                                            | None  ->
                                                let uu____4226 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4226 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4233 =
                                                         let uu____4234 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4234 =
                                                           cache_size in
                                                       if uu____4233
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls decls' in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         Prims.snd cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4245 =
                                                           let uu____4246 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4246 in
                                                         varops.mk_unique
                                                           uu____4245 in
                                                       Prims.strcat
                                                         module_name
                                                         (Prims.strcat "_"
                                                            fsym) in
                                                     let fdecl =
                                                       FStar_SMTEncoding_Term.DeclFun
                                                         (fsym, cvar_sorts,
                                                           FStar_SMTEncoding_Term.Term_sort,
                                                           None) in
                                                     let f =
                                                       let uu____4251 =
                                                         let uu____4255 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4255) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4251 in
                                                     let app =
                                                       mk_Apply f vars in
                                                     let typing_f =
                                                       match arrow_t_opt with
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1 in
                                                           let a_name =
                                                             Prims.strcat
                                                               "typing_" fsym in
                                                           let uu____4267 =
                                                             let uu____4268 =
                                                               let uu____4272
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4272,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4268 in
                                                           [uu____4267] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4280 =
                                                         let uu____4284 =
                                                           let uu____4285 =
                                                             let uu____4291 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4291) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4285 in
                                                         (uu____4284,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4280 in
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
                                                     ((let uu____4301 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4301);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4303,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4304;
                          FStar_Syntax_Syntax.lbunivs = uu____4305;
                          FStar_Syntax_Syntax.lbtyp = uu____4306;
                          FStar_Syntax_Syntax.lbeff = uu____4307;
                          FStar_Syntax_Syntax.lbdef = uu____4308;_}::uu____4309),uu____4310)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4328;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4330;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4346 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4359 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4359, [decl_e])))
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
                 (FStar_SMTEncoding_Term.term*
                   FStar_SMTEncoding_Term.decls_t))
              ->
              (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun x  ->
    fun t1  ->
      fun e1  ->
        fun e2  ->
          fun env  ->
            fun encode_body  ->
              let uu____4401 = encode_term e1 env in
              match uu____4401 with
              | (ee1,decls1) ->
                  let uu____4408 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4408 with
                   | (xs,e21) ->
                       let uu____4422 = FStar_List.hd xs in
                       (match uu____4422 with
                        | (x1,uu____4430) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4432 = encode_body e21 env' in
                            (match uu____4432 with
                             | (ee2,decls2) ->
                                 (ee2, (FStar_List.append decls1 decls2)))))
and encode_match:
  FStar_Syntax_Syntax.term ->
    FStar_Syntax_Syntax.branch Prims.list ->
      FStar_SMTEncoding_Term.term ->
        env_t ->
          (FStar_Syntax_Syntax.term ->
             env_t ->
               (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____4454 =
              let uu____4458 =
                let uu____4459 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4459 in
              gen_term_var env uu____4458 in
            match uu____4454 with
            | (scrsym,scr',env1) ->
                let uu____4473 = encode_term e env1 in
                (match uu____4473 with
                 | (scr,decls) ->
                     let uu____4480 =
                       let encode_branch b uu____4496 =
                         match uu____4496 with
                         | (else_case,decls1) ->
                             let uu____4507 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4507 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4537  ->
                                       fun uu____4538  ->
                                         match (uu____4537, uu____4538) with
                                         | ((env0,pattern),(else_case1,decls2))
                                             ->
                                             let guard = pattern.guard scr' in
                                             let projections =
                                               pattern.projections scr' in
                                             let env2 =
                                               FStar_All.pipe_right
                                                 projections
                                                 (FStar_List.fold_left
                                                    (fun env2  ->
                                                       fun uu____4575  ->
                                                         match uu____4575
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4580 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4595 =
                                                     encode_term w1 env2 in
                                                   (match uu____4595 with
                                                    | (w2,decls21) ->
                                                        let uu____4603 =
                                                          let uu____4604 =
                                                            let uu____4607 =
                                                              let uu____4608
                                                                =
                                                                let uu____4611
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4611) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4608 in
                                                            (guard,
                                                              uu____4607) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4604 in
                                                        (uu____4603, decls21)) in
                                             (match uu____4580 with
                                              | (guard1,decls21) ->
                                                  let uu____4619 =
                                                    encode_br br env2 in
                                                  (match uu____4619 with
                                                   | (br1,decls3) ->
                                                       let uu____4627 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4627,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4480 with
                      | (match_tm,decls1) ->
                          let uu____4639 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4639, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4670 -> let uu____4671 = encode_one_pat env pat in [uu____4671]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4683 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4683
       then
         let uu____4684 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4684
       else ());
      (let uu____4686 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4686 with
       | (vars,pat_term) ->
           let uu____4696 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4719  ->
                     fun v1  ->
                       match uu____4719 with
                       | (env1,vars1) ->
                           let uu____4747 = gen_term_var env1 v1 in
                           (match uu____4747 with
                            | (xx,uu____4759,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4696 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4806 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4814 =
                        let uu____4817 = encode_const c in
                        (scrutinee, uu____4817) in
                      FStar_SMTEncoding_Util.mkEq uu____4814
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4836 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4836 with
                        | (uu____4840,uu____4841::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4843 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4864  ->
                                  match uu____4864 with
                                  | (arg,uu____4870) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4880 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4880)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4899 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4914 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4929 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4951  ->
                                  match uu____4951 with
                                  | (arg,uu____4960) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4970 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4970)) in
                      FStar_All.pipe_right uu____4929 FStar_List.flatten in
                let pat_term1 uu____4986 = encode_term pat_term env1 in
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
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
  =
  fun l  ->
    fun env  ->
      let uu____4993 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5008  ->
                fun uu____5009  ->
                  match (uu____5008, uu____5009) with
                  | ((tms,decls),(t,uu____5029)) ->
                      let uu____5040 = encode_term t env in
                      (match uu____5040 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4993 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun new_pats  ->
    fun t  ->
      fun env  ->
        let list_elements1 e =
          let uu____5076 = FStar_Syntax_Util.list_elements e in
          match uu____5076 with
          | Some l -> l
          | None  ->
              (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                 "SMT pattern is not a list literal; ignoring the pattern";
               []) in
        let one_pat p =
          let uu____5091 =
            let uu____5101 = FStar_Syntax_Util.unmeta p in
            FStar_All.pipe_right uu____5101 FStar_Syntax_Util.head_and_args in
          match uu____5091 with
          | (head1,args) ->
              let uu____5129 =
                let uu____5137 =
                  let uu____5138 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5138.FStar_Syntax_Syntax.n in
                (uu____5137, args) in
              (match uu____5129 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,(uu____5149,uu____5150)::(e,uu____5152)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpat_lid
                   -> e
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5180)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatT_lid
                   -> e
               | uu____5198 -> failwith "Unexpected pattern term") in
        let lemma_pats p =
          let elts = list_elements1 p in
          let smt_pat_or t1 =
            let uu____5225 =
              let uu____5235 = FStar_Syntax_Util.unmeta t1 in
              FStar_All.pipe_right uu____5235 FStar_Syntax_Util.head_and_args in
            match uu____5225 with
            | (head1,args) ->
                let uu____5264 =
                  let uu____5272 =
                    let uu____5273 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5273.FStar_Syntax_Syntax.n in
                  (uu____5272, args) in
                (match uu____5264 with
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5286)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatOr_lid
                     -> Some e
                 | uu____5306 -> None) in
          match elts with
          | t1::[] ->
              let uu____5321 = smt_pat_or t1 in
              (match uu____5321 with
               | Some e ->
                   let uu____5334 = list_elements1 e in
                   FStar_All.pipe_right uu____5334
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5345 = list_elements1 branch1 in
                           FStar_All.pipe_right uu____5345
                             (FStar_List.map one_pat)))
               | uu____5353 ->
                   let uu____5357 =
                     FStar_All.pipe_right elts (FStar_List.map one_pat) in
                   [uu____5357])
          | uu____5373 ->
              let uu____5375 =
                FStar_All.pipe_right elts (FStar_List.map one_pat) in
              [uu____5375] in
        let uu____5391 =
          let uu____5404 =
            let uu____5405 = FStar_Syntax_Subst.compress t in
            uu____5405.FStar_Syntax_Syntax.n in
          match uu____5404 with
          | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
              let uu____5432 = FStar_Syntax_Subst.open_comp binders c in
              (match uu____5432 with
               | (binders1,c1) ->
                   (match c1.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Comp
                        { FStar_Syntax_Syntax.comp_univs = uu____5461;
                          FStar_Syntax_Syntax.effect_name = uu____5462;
                          FStar_Syntax_Syntax.result_typ = uu____5463;
                          FStar_Syntax_Syntax.effect_args =
                            (pre,uu____5465)::(post,uu____5467)::(pats,uu____5469)::[];
                          FStar_Syntax_Syntax.flags = uu____5470;_}
                        ->
                        let pats' =
                          match new_pats with
                          | Some new_pats' -> new_pats'
                          | None  -> pats in
                        let uu____5504 = lemma_pats pats' in
                        (binders1, pre, post, uu____5504)
                    | uu____5517 -> failwith "impos"))
          | uu____5530 -> failwith "Impos" in
        match uu____5391 with
        | (binders,pre,post,patterns) ->
            let env1 =
              let uu___140_5566 = env in
              let uu____5567 =
                let uu____5569 =
                  FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0") in
                Some uu____5569 in
              {
                bindings = (uu___140_5566.bindings);
                depth = (uu___140_5566.depth);
                tcenv = (uu___140_5566.tcenv);
                warn = (uu___140_5566.warn);
                cache = (uu___140_5566.cache);
                nolabels = (uu___140_5566.nolabels);
                use_fuel_instrumented_version = uu____5567;
                encode_non_total_function_typ =
                  (uu___140_5566.encode_non_total_function_typ);
                current_module_name = (uu___140_5566.current_module_name)
              } in
            let uu____5570 = encode_binders None binders env1 in
            (match uu____5570 with
             | (vars,guards,env2,decls,uu____5585) ->
                 let uu____5592 =
                   let env3 =
                     let uu___141_5600 = env2 in
                     let uu____5601 =
                       let uu____5603 =
                         FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
                       Some uu____5603 in
                     {
                       bindings = (uu___141_5600.bindings);
                       depth = (uu___141_5600.depth);
                       tcenv = (uu___141_5600.tcenv);
                       warn = (uu___141_5600.warn);
                       cache = (uu___141_5600.cache);
                       nolabels = (uu___141_5600.nolabels);
                       use_fuel_instrumented_version = uu____5601;
                       encode_non_total_function_typ =
                         (uu___141_5600.encode_non_total_function_typ);
                       current_module_name =
                         (uu___141_5600.current_module_name)
                     } in
                   let uu____5604 =
                     FStar_All.pipe_right patterns
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5626 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env3)) in
                             FStar_All.pipe_right uu____5626 FStar_List.unzip)) in
                   FStar_All.pipe_right uu____5604 FStar_List.unzip in
                 (match uu____5592 with
                  | (pats,decls') ->
                      let decls'1 = FStar_List.flatten decls' in
                      let env3 =
                        let uu___142_5672 = env2 in
                        {
                          bindings = (uu___142_5672.bindings);
                          depth = (uu___142_5672.depth);
                          tcenv = (uu___142_5672.tcenv);
                          warn = (uu___142_5672.warn);
                          cache = (uu___142_5672.cache);
                          nolabels = true;
                          use_fuel_instrumented_version =
                            (uu___142_5672.use_fuel_instrumented_version);
                          encode_non_total_function_typ =
                            (uu___142_5672.encode_non_total_function_typ);
                          current_module_name =
                            (uu___142_5672.current_module_name)
                        } in
                      let uu____5673 =
                        let uu____5676 = FStar_Syntax_Util.unmeta pre in
                        encode_formula uu____5676 env3 in
                      (match uu____5673 with
                       | (pre1,decls'') ->
                           let uu____5681 =
                             let uu____5684 = FStar_Syntax_Util.unmeta post in
                             encode_formula uu____5684 env3 in
                           (match uu____5681 with
                            | (post1,decls''') ->
                                let decls1 =
                                  FStar_List.append decls
                                    (FStar_List.append
                                       (FStar_List.flatten decls'1)
                                       (FStar_List.append decls'' decls''')) in
                                let uu____5691 =
                                  let uu____5692 =
                                    let uu____5698 =
                                      let uu____5699 =
                                        let uu____5702 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            (pre1 :: guards) in
                                        (uu____5702, post1) in
                                      FStar_SMTEncoding_Util.mkImp uu____5699 in
                                    (pats, vars, uu____5698) in
                                  FStar_SMTEncoding_Util.mkForall uu____5692 in
                                (uu____5691, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5715 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5715
        then
          let uu____5716 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5717 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5716 uu____5717
        else () in
      let enc f r l =
        let uu____5744 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5757 = encode_term (Prims.fst x) env in
                 match uu____5757 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5744 with
        | (decls,args) ->
            let uu____5774 =
              let uu___143_5775 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___143_5775.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___143_5775.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5774, decls) in
      let const_op f r uu____5794 = let uu____5797 = f r in (uu____5797, []) in
      let un_op f l =
        let uu____5813 = FStar_List.hd l in FStar_All.pipe_left f uu____5813 in
      let bin_op f uu___114_5826 =
        match uu___114_5826 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5834 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5861 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5870  ->
                 match uu____5870 with
                 | (t,uu____5878) ->
                     let uu____5879 = encode_formula t env in
                     (match uu____5879 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____5861 with
        | (decls,phis) ->
            let uu____5896 =
              let uu___144_5897 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_5897.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_5897.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5896, decls) in
      let eq_op r uu___115_5913 =
        match uu___115_5913 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____5973 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____5973 r [e1; e2]
        | l ->
            let uu____5993 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____5993 r l in
      let mk_imp1 r uu___116_6012 =
        match uu___116_6012 with
        | (lhs,uu____6016)::(rhs,uu____6018)::[] ->
            let uu____6039 = encode_formula rhs env in
            (match uu____6039 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6048) ->
                      (l1, decls1)
                  | uu____6051 ->
                      let uu____6052 = encode_formula lhs env in
                      (match uu____6052 with
                       | (l2,decls2) ->
                           let uu____6059 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6059, (FStar_List.append decls1 decls2)))))
        | uu____6061 -> failwith "impossible" in
      let mk_ite r uu___117_6076 =
        match uu___117_6076 with
        | (guard,uu____6080)::(_then,uu____6082)::(_else,uu____6084)::[] ->
            let uu____6113 = encode_formula guard env in
            (match uu____6113 with
             | (g,decls1) ->
                 let uu____6120 = encode_formula _then env in
                 (match uu____6120 with
                  | (t,decls2) ->
                      let uu____6127 = encode_formula _else env in
                      (match uu____6127 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6136 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6155 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6155 in
      let connectives =
        let uu____6167 =
          let uu____6176 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6176) in
        let uu____6189 =
          let uu____6199 =
            let uu____6208 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6208) in
          let uu____6221 =
            let uu____6231 =
              let uu____6241 =
                let uu____6250 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6250) in
              let uu____6263 =
                let uu____6273 =
                  let uu____6283 =
                    let uu____6292 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6292) in
                  [uu____6283;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6273 in
              uu____6241 :: uu____6263 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6231 in
          uu____6199 :: uu____6221 in
        uu____6167 :: uu____6189 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6454 = encode_formula phi' env in
            (match uu____6454 with
             | (phi2,decls) ->
                 let uu____6461 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6461, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6462 ->
            let uu____6467 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6467 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6496 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6496 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6504;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6506;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6522 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6522 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6554::(x,uu____6556)::(t,uu____6558)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6592 = encode_term x env in
                 (match uu____6592 with
                  | (x1,decls) ->
                      let uu____6599 = encode_term t env in
                      (match uu____6599 with
                       | (t1,decls') ->
                           let uu____6606 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6606, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6610)::(msg,uu____6612)::(phi2,uu____6614)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6648 =
                   let uu____6651 =
                     let uu____6652 = FStar_Syntax_Subst.compress r in
                     uu____6652.FStar_Syntax_Syntax.n in
                   let uu____6655 =
                     let uu____6656 = FStar_Syntax_Subst.compress msg in
                     uu____6656.FStar_Syntax_Syntax.n in
                   (uu____6651, uu____6655) in
                 (match uu____6648 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6663))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6679 -> fallback phi2)
             | uu____6682 when head_redex env head2 ->
                 let uu____6690 = whnf env phi1 in
                 encode_formula uu____6690 env
             | uu____6691 ->
                 let uu____6699 = encode_term phi1 env in
                 (match uu____6699 with
                  | (tt,decls) ->
                      let uu____6706 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___145_6707 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___145_6707.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___145_6707.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6706, decls)))
        | uu____6710 ->
            let uu____6711 = encode_term phi1 env in
            (match uu____6711 with
             | (tt,decls) ->
                 let uu____6718 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___146_6719 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___146_6719.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___146_6719.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6718, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6746 = encode_binders None bs env1 in
        match uu____6746 with
        | (vars,guards,env2,decls,uu____6768) ->
            let uu____6775 =
              let uu____6782 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6805 =
                          let uu____6810 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6824  ->
                                    match uu____6824 with
                                    | (t,uu____6830) ->
                                        let uu____6831 =
                                          let uu___147_6832 = env2 in
                                          let uu____6833 =
                                            let uu____6835 =
                                              FStar_SMTEncoding_Term.n_fuel
                                                (Prims.parse_int "0") in
                                            Some uu____6835 in
                                          {
                                            bindings =
                                              (uu___147_6832.bindings);
                                            depth = (uu___147_6832.depth);
                                            tcenv = (uu___147_6832.tcenv);
                                            warn = (uu___147_6832.warn);
                                            cache = (uu___147_6832.cache);
                                            nolabels =
                                              (uu___147_6832.nolabels);
                                            use_fuel_instrumented_version =
                                              uu____6833;
                                            encode_non_total_function_typ =
                                              (uu___147_6832.encode_non_total_function_typ);
                                            current_module_name =
                                              (uu___147_6832.current_module_name)
                                          } in
                                        encode_term t uu____6831)) in
                          FStar_All.pipe_right uu____6810 FStar_List.unzip in
                        match uu____6805 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6782 FStar_List.unzip in
            (match uu____6775 with
             | (pats,decls') ->
                 let uu____6887 = encode_formula body env2 in
                 (match uu____6887 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6906;
                             FStar_SMTEncoding_Term.rng = uu____6907;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6915 -> guards in
                      let uu____6918 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____6918, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____6952  ->
                   match uu____6952 with
                   | (x,uu____6956) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____6962 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____6968 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____6968) uu____6962 tl1 in
             let uu____6970 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6982  ->
                       match uu____6982 with
                       | (b,uu____6986) ->
                           let uu____6987 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____6987)) in
             (match uu____6970 with
              | None  -> ()
              | Some (x,uu____6991) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7001 =
                    let uu____7002 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7002 in
                  FStar_Errors.warn pos uu____7001) in
       let uu____7003 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7003 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7009 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7045  ->
                     match uu____7045 with
                     | (l,uu____7055) -> FStar_Ident.lid_equals op l)) in
           (match uu____7009 with
            | None  -> fallback phi1
            | Some (uu____7078,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7107 = encode_q_body env vars pats body in
             match uu____7107 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7133 =
                     let uu____7139 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7139) in
                   FStar_SMTEncoding_Term.mkForall uu____7133
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7151 = encode_q_body env vars pats body in
             match uu____7151 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7176 =
                   let uu____7177 =
                     let uu____7183 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7183) in
                   FStar_SMTEncoding_Term.mkExists uu____7177
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7176, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7232 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7232 with
  | (asym,a) ->
      let uu____7237 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7237 with
       | (xsym,x) ->
           let uu____7242 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7242 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7272 =
                      let uu____7278 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7278, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7272 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7293 =
                      let uu____7297 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7297) in
                    FStar_SMTEncoding_Util.mkApp uu____7293 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7305 =
                    let uu____7307 =
                      let uu____7309 =
                        let uu____7311 =
                          let uu____7312 =
                            let uu____7316 =
                              let uu____7317 =
                                let uu____7323 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7323) in
                              FStar_SMTEncoding_Util.mkForall uu____7317 in
                            (uu____7316, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7312 in
                        let uu____7332 =
                          let uu____7334 =
                            let uu____7335 =
                              let uu____7339 =
                                let uu____7340 =
                                  let uu____7346 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7346) in
                                FStar_SMTEncoding_Util.mkForall uu____7340 in
                              (uu____7339,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7335 in
                          [uu____7334] in
                        uu____7311 :: uu____7332 in
                      xtok_decl :: uu____7309 in
                    xname_decl :: uu____7307 in
                  (xtok1, uu____7305) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7395 =
                    let uu____7403 =
                      let uu____7409 =
                        let uu____7410 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7410 in
                      quant axy uu____7409 in
                    (FStar_Syntax_Const.op_Eq, uu____7403) in
                  let uu____7416 =
                    let uu____7425 =
                      let uu____7433 =
                        let uu____7439 =
                          let uu____7440 =
                            let uu____7441 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7441 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7440 in
                        quant axy uu____7439 in
                      (FStar_Syntax_Const.op_notEq, uu____7433) in
                    let uu____7447 =
                      let uu____7456 =
                        let uu____7464 =
                          let uu____7470 =
                            let uu____7471 =
                              let uu____7472 =
                                let uu____7475 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7476 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7475, uu____7476) in
                              FStar_SMTEncoding_Util.mkLT uu____7472 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7471 in
                          quant xy uu____7470 in
                        (FStar_Syntax_Const.op_LT, uu____7464) in
                      let uu____7482 =
                        let uu____7491 =
                          let uu____7499 =
                            let uu____7505 =
                              let uu____7506 =
                                let uu____7507 =
                                  let uu____7510 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7511 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7510, uu____7511) in
                                FStar_SMTEncoding_Util.mkLTE uu____7507 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7506 in
                            quant xy uu____7505 in
                          (FStar_Syntax_Const.op_LTE, uu____7499) in
                        let uu____7517 =
                          let uu____7526 =
                            let uu____7534 =
                              let uu____7540 =
                                let uu____7541 =
                                  let uu____7542 =
                                    let uu____7545 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7546 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7545, uu____7546) in
                                  FStar_SMTEncoding_Util.mkGT uu____7542 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7541 in
                              quant xy uu____7540 in
                            (FStar_Syntax_Const.op_GT, uu____7534) in
                          let uu____7552 =
                            let uu____7561 =
                              let uu____7569 =
                                let uu____7575 =
                                  let uu____7576 =
                                    let uu____7577 =
                                      let uu____7580 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7581 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7580, uu____7581) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7577 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7576 in
                                quant xy uu____7575 in
                              (FStar_Syntax_Const.op_GTE, uu____7569) in
                            let uu____7587 =
                              let uu____7596 =
                                let uu____7604 =
                                  let uu____7610 =
                                    let uu____7611 =
                                      let uu____7612 =
                                        let uu____7615 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7616 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7615, uu____7616) in
                                      FStar_SMTEncoding_Util.mkSub uu____7612 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7611 in
                                  quant xy uu____7610 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7604) in
                              let uu____7622 =
                                let uu____7631 =
                                  let uu____7639 =
                                    let uu____7645 =
                                      let uu____7646 =
                                        let uu____7647 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7647 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7646 in
                                    quant qx uu____7645 in
                                  (FStar_Syntax_Const.op_Minus, uu____7639) in
                                let uu____7653 =
                                  let uu____7662 =
                                    let uu____7670 =
                                      let uu____7676 =
                                        let uu____7677 =
                                          let uu____7678 =
                                            let uu____7681 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7682 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7681, uu____7682) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7678 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7677 in
                                      quant xy uu____7676 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7670) in
                                  let uu____7688 =
                                    let uu____7697 =
                                      let uu____7705 =
                                        let uu____7711 =
                                          let uu____7712 =
                                            let uu____7713 =
                                              let uu____7716 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7717 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7716, uu____7717) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7713 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7712 in
                                        quant xy uu____7711 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7705) in
                                    let uu____7723 =
                                      let uu____7732 =
                                        let uu____7740 =
                                          let uu____7746 =
                                            let uu____7747 =
                                              let uu____7748 =
                                                let uu____7751 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7752 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7751, uu____7752) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7748 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7747 in
                                          quant xy uu____7746 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7740) in
                                      let uu____7758 =
                                        let uu____7767 =
                                          let uu____7775 =
                                            let uu____7781 =
                                              let uu____7782 =
                                                let uu____7783 =
                                                  let uu____7786 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7787 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7786, uu____7787) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7783 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7782 in
                                            quant xy uu____7781 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7775) in
                                        let uu____7793 =
                                          let uu____7802 =
                                            let uu____7810 =
                                              let uu____7816 =
                                                let uu____7817 =
                                                  let uu____7818 =
                                                    let uu____7821 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7822 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7821, uu____7822) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7818 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7817 in
                                              quant xy uu____7816 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7810) in
                                          let uu____7828 =
                                            let uu____7837 =
                                              let uu____7845 =
                                                let uu____7851 =
                                                  let uu____7852 =
                                                    let uu____7853 =
                                                      let uu____7856 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7857 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7856,
                                                        uu____7857) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7853 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7852 in
                                                quant xy uu____7851 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7845) in
                                            let uu____7863 =
                                              let uu____7872 =
                                                let uu____7880 =
                                                  let uu____7886 =
                                                    let uu____7887 =
                                                      let uu____7888 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7888 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7887 in
                                                  quant qx uu____7886 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7880) in
                                              [uu____7872] in
                                            uu____7837 :: uu____7863 in
                                          uu____7802 :: uu____7828 in
                                        uu____7767 :: uu____7793 in
                                      uu____7732 :: uu____7758 in
                                    uu____7697 :: uu____7723 in
                                  uu____7662 :: uu____7688 in
                                uu____7631 :: uu____7653 in
                              uu____7596 :: uu____7622 in
                            uu____7561 :: uu____7587 in
                          uu____7526 :: uu____7552 in
                        uu____7491 :: uu____7517 in
                      uu____7456 :: uu____7482 in
                    uu____7425 :: uu____7447 in
                  uu____7395 :: uu____7416 in
                let mk1 l v1 =
                  let uu____8016 =
                    let uu____8021 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8053  ->
                              match uu____8053 with
                              | (l',uu____8062) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8021
                      (FStar_Option.map
                         (fun uu____8095  ->
                            match uu____8095 with | (uu____8106,b) -> b v1)) in
                  FStar_All.pipe_right uu____8016 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8147  ->
                          match uu____8147 with
                          | (l',uu____8156) -> FStar_Ident.lid_equals l l')) in
                { mk = mk1; is }))
let pretype_axiom:
  env_t ->
    FStar_SMTEncoding_Term.term ->
      (Prims.string* FStar_SMTEncoding_Term.sort) Prims.list ->
        FStar_SMTEncoding_Term.decl
  =
  fun env  ->
    fun tapp  ->
      fun vars  ->
        let uu____8182 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8182 with
        | (xxsym,xx) ->
            let uu____8187 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8187 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8195 =
                   let uu____8199 =
                     let uu____8200 =
                       let uu____8206 =
                         let uu____8207 =
                           let uu____8210 =
                             let uu____8211 =
                               let uu____8214 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8214) in
                             FStar_SMTEncoding_Util.mkEq uu____8211 in
                           (xx_has_type, uu____8210) in
                         FStar_SMTEncoding_Util.mkImp uu____8207 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8206) in
                     FStar_SMTEncoding_Util.mkForall uu____8200 in
                   let uu____8227 =
                     let uu____8228 =
                       let uu____8229 =
                         let uu____8230 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8230 in
                       Prims.strcat module_name uu____8229 in
                     varops.mk_unique uu____8228 in
                   (uu____8199, (Some "pretyping"), uu____8227) in
                 FStar_SMTEncoding_Util.mkAssume uu____8195)
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
    let uu____8260 =
      let uu____8261 =
        let uu____8265 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8265, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8261 in
    let uu____8267 =
      let uu____8269 =
        let uu____8270 =
          let uu____8274 =
            let uu____8275 =
              let uu____8281 =
                let uu____8282 =
                  let uu____8285 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8285) in
                FStar_SMTEncoding_Util.mkImp uu____8282 in
              ([[typing_pred]], [xx], uu____8281) in
            mkForall_fuel uu____8275 in
          (uu____8274, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8270 in
      [uu____8269] in
    uu____8260 :: uu____8267 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8313 =
      let uu____8314 =
        let uu____8318 =
          let uu____8319 =
            let uu____8325 =
              let uu____8328 =
                let uu____8330 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8330] in
              [uu____8328] in
            let uu____8333 =
              let uu____8334 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8334 tt in
            (uu____8325, [bb], uu____8333) in
          FStar_SMTEncoding_Util.mkForall uu____8319 in
        (uu____8318, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8314 in
    let uu____8345 =
      let uu____8347 =
        let uu____8348 =
          let uu____8352 =
            let uu____8353 =
              let uu____8359 =
                let uu____8360 =
                  let uu____8363 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8363) in
                FStar_SMTEncoding_Util.mkImp uu____8360 in
              ([[typing_pred]], [xx], uu____8359) in
            mkForall_fuel uu____8353 in
          (uu____8352, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8348 in
      [uu____8347] in
    uu____8313 :: uu____8345 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8397 =
        let uu____8398 =
          let uu____8402 =
            let uu____8404 =
              let uu____8406 =
                let uu____8408 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8409 =
                  let uu____8411 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8411] in
                uu____8408 :: uu____8409 in
              tt :: uu____8406 in
            tt :: uu____8404 in
          ("Prims.Precedes", uu____8402) in
        FStar_SMTEncoding_Util.mkApp uu____8398 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8397 in
    let precedes_y_x =
      let uu____8414 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8414 in
    let uu____8416 =
      let uu____8417 =
        let uu____8421 =
          let uu____8422 =
            let uu____8428 =
              let uu____8431 =
                let uu____8433 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8433] in
              [uu____8431] in
            let uu____8436 =
              let uu____8437 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8437 tt in
            (uu____8428, [bb], uu____8436) in
          FStar_SMTEncoding_Util.mkForall uu____8422 in
        (uu____8421, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8417 in
    let uu____8448 =
      let uu____8450 =
        let uu____8451 =
          let uu____8455 =
            let uu____8456 =
              let uu____8462 =
                let uu____8463 =
                  let uu____8466 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8466) in
                FStar_SMTEncoding_Util.mkImp uu____8463 in
              ([[typing_pred]], [xx], uu____8462) in
            mkForall_fuel uu____8456 in
          (uu____8455, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8451 in
      let uu____8479 =
        let uu____8481 =
          let uu____8482 =
            let uu____8486 =
              let uu____8487 =
                let uu____8493 =
                  let uu____8494 =
                    let uu____8497 =
                      let uu____8498 =
                        let uu____8500 =
                          let uu____8502 =
                            let uu____8504 =
                              let uu____8505 =
                                let uu____8508 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8509 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8508, uu____8509) in
                              FStar_SMTEncoding_Util.mkGT uu____8505 in
                            let uu____8510 =
                              let uu____8512 =
                                let uu____8513 =
                                  let uu____8516 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8517 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8516, uu____8517) in
                                FStar_SMTEncoding_Util.mkGTE uu____8513 in
                              let uu____8518 =
                                let uu____8520 =
                                  let uu____8521 =
                                    let uu____8524 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8525 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8524, uu____8525) in
                                  FStar_SMTEncoding_Util.mkLT uu____8521 in
                                [uu____8520] in
                              uu____8512 :: uu____8518 in
                            uu____8504 :: uu____8510 in
                          typing_pred_y :: uu____8502 in
                        typing_pred :: uu____8500 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8498 in
                    (uu____8497, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8494 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8493) in
              mkForall_fuel uu____8487 in
            (uu____8486, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8482 in
        [uu____8481] in
      uu____8450 :: uu____8479 in
    uu____8416 :: uu____8448 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8555 =
      let uu____8556 =
        let uu____8560 =
          let uu____8561 =
            let uu____8567 =
              let uu____8570 =
                let uu____8572 = FStar_SMTEncoding_Term.boxString b in
                [uu____8572] in
              [uu____8570] in
            let uu____8575 =
              let uu____8576 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8576 tt in
            (uu____8567, [bb], uu____8575) in
          FStar_SMTEncoding_Util.mkForall uu____8561 in
        (uu____8560, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8556 in
    let uu____8587 =
      let uu____8589 =
        let uu____8590 =
          let uu____8594 =
            let uu____8595 =
              let uu____8601 =
                let uu____8602 =
                  let uu____8605 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8605) in
                FStar_SMTEncoding_Util.mkImp uu____8602 in
              ([[typing_pred]], [xx], uu____8601) in
            mkForall_fuel uu____8595 in
          (uu____8594, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8590 in
      [uu____8589] in
    uu____8555 :: uu____8587 in
  let mk_ref1 env reft_name uu____8627 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8638 =
        let uu____8642 =
          let uu____8644 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8644] in
        (reft_name, uu____8642) in
      FStar_SMTEncoding_Util.mkApp uu____8638 in
    let refb =
      let uu____8647 =
        let uu____8651 =
          let uu____8653 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8653] in
        (reft_name, uu____8651) in
      FStar_SMTEncoding_Util.mkApp uu____8647 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8657 =
      let uu____8658 =
        let uu____8662 =
          let uu____8663 =
            let uu____8669 =
              let uu____8670 =
                let uu____8673 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8673) in
              FStar_SMTEncoding_Util.mkImp uu____8670 in
            ([[typing_pred]], [xx; aa], uu____8669) in
          mkForall_fuel uu____8663 in
        (uu____8662, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8658 in
    [uu____8657] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8713 =
      let uu____8714 =
        let uu____8718 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8718, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8714 in
    [uu____8713] in
  let mk_and_interp env conj uu____8729 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8746 =
      let uu____8747 =
        let uu____8751 =
          let uu____8752 =
            let uu____8758 =
              let uu____8759 =
                let uu____8762 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8762, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8759 in
            ([[l_and_a_b]], [aa; bb], uu____8758) in
          FStar_SMTEncoding_Util.mkForall uu____8752 in
        (uu____8751, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8747 in
    [uu____8746] in
  let mk_or_interp env disj uu____8786 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8803 =
      let uu____8804 =
        let uu____8808 =
          let uu____8809 =
            let uu____8815 =
              let uu____8816 =
                let uu____8819 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8819, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8816 in
            ([[l_or_a_b]], [aa; bb], uu____8815) in
          FStar_SMTEncoding_Util.mkForall uu____8809 in
        (uu____8808, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8804 in
    [uu____8803] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____8860 =
      let uu____8861 =
        let uu____8865 =
          let uu____8866 =
            let uu____8872 =
              let uu____8873 =
                let uu____8876 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8876, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8873 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____8872) in
          FStar_SMTEncoding_Util.mkForall uu____8866 in
        (uu____8865, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8861 in
    [uu____8860] in
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
    let uu____8923 =
      let uu____8924 =
        let uu____8928 =
          let uu____8929 =
            let uu____8935 =
              let uu____8936 =
                let uu____8939 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8939, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8936 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____8935) in
          FStar_SMTEncoding_Util.mkForall uu____8929 in
        (uu____8928, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8924 in
    [uu____8923] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8984 =
      let uu____8985 =
        let uu____8989 =
          let uu____8990 =
            let uu____8996 =
              let uu____8997 =
                let uu____9000 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9000, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8997 in
            ([[l_imp_a_b]], [aa; bb], uu____8996) in
          FStar_SMTEncoding_Util.mkForall uu____8990 in
        (uu____8989, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8985 in
    [uu____8984] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9041 =
      let uu____9042 =
        let uu____9046 =
          let uu____9047 =
            let uu____9053 =
              let uu____9054 =
                let uu____9057 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9057, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9054 in
            ([[l_iff_a_b]], [aa; bb], uu____9053) in
          FStar_SMTEncoding_Util.mkForall uu____9047 in
        (uu____9046, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9042 in
    [uu____9041] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9091 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9091 in
    let uu____9093 =
      let uu____9094 =
        let uu____9098 =
          let uu____9099 =
            let uu____9105 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9105) in
          FStar_SMTEncoding_Util.mkForall uu____9099 in
        (uu____9098, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9094 in
    [uu____9093] in
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
      let uu____9145 =
        let uu____9149 =
          let uu____9151 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9151] in
        ("Valid", uu____9149) in
      FStar_SMTEncoding_Util.mkApp uu____9145 in
    let uu____9153 =
      let uu____9154 =
        let uu____9158 =
          let uu____9159 =
            let uu____9165 =
              let uu____9166 =
                let uu____9169 =
                  let uu____9170 =
                    let uu____9176 =
                      let uu____9179 =
                        let uu____9181 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9181] in
                      [uu____9179] in
                    let uu____9184 =
                      let uu____9185 =
                        let uu____9188 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9188, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9185 in
                    (uu____9176, [xx1], uu____9184) in
                  FStar_SMTEncoding_Util.mkForall uu____9170 in
                (uu____9169, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9166 in
            ([[l_forall_a_b]], [aa; bb], uu____9165) in
          FStar_SMTEncoding_Util.mkForall uu____9159 in
        (uu____9158, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9154 in
    [uu____9153] in
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
      let uu____9239 =
        let uu____9243 =
          let uu____9245 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9245] in
        ("Valid", uu____9243) in
      FStar_SMTEncoding_Util.mkApp uu____9239 in
    let uu____9247 =
      let uu____9248 =
        let uu____9252 =
          let uu____9253 =
            let uu____9259 =
              let uu____9260 =
                let uu____9263 =
                  let uu____9264 =
                    let uu____9270 =
                      let uu____9273 =
                        let uu____9275 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9275] in
                      [uu____9273] in
                    let uu____9278 =
                      let uu____9279 =
                        let uu____9282 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9282, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9279 in
                    (uu____9270, [xx1], uu____9278) in
                  FStar_SMTEncoding_Util.mkExists uu____9264 in
                (uu____9263, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9260 in
            ([[l_exists_a_b]], [aa; bb], uu____9259) in
          FStar_SMTEncoding_Util.mkForall uu____9253 in
        (uu____9252, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9248 in
    [uu____9247] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9318 =
      let uu____9319 =
        let uu____9323 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9324 = varops.mk_unique "typing_range_const" in
        (uu____9323, (Some "Range_const typing"), uu____9324) in
      FStar_SMTEncoding_Util.mkAssume uu____9319 in
    [uu____9318] in
  let prims1 =
    [(FStar_Syntax_Const.unit_lid, mk_unit);
    (FStar_Syntax_Const.bool_lid, mk_bool);
    (FStar_Syntax_Const.int_lid, mk_int);
    (FStar_Syntax_Const.string_lid, mk_str);
    (FStar_Syntax_Const.ref_lid, mk_ref1);
    (FStar_Syntax_Const.true_lid, mk_true_interp);
    (FStar_Syntax_Const.false_lid, mk_false_interp);
    (FStar_Syntax_Const.and_lid, mk_and_interp);
    (FStar_Syntax_Const.or_lid, mk_or_interp);
    (FStar_Syntax_Const.eq2_lid, mk_eq2_interp);
    (FStar_Syntax_Const.eq3_lid, mk_eq3_interp);
    (FStar_Syntax_Const.imp_lid, mk_imp_interp);
    (FStar_Syntax_Const.iff_lid, mk_iff_interp);
    (FStar_Syntax_Const.not_lid, mk_not_interp);
    (FStar_Syntax_Const.forall_lid, mk_forall_interp);
    (FStar_Syntax_Const.exists_lid, mk_exists_interp);
    (FStar_Syntax_Const.range_lid, mk_range_interp)] in
  fun env  ->
    fun t  ->
      fun s  ->
        fun tt  ->
          let uu____9586 =
            FStar_Util.find_opt
              (fun uu____9604  ->
                 match uu____9604 with
                 | (l,uu____9614) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9586 with
          | None  -> []
          | Some (uu____9636,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9673 = encode_function_type_as_formula None t env in
        match uu____9673 with
        | (form,decls) ->
            FStar_List.append decls
              [FStar_SMTEncoding_Util.mkAssume
                 (form, (Some (Prims.strcat "Lemma: " lid.FStar_Ident.str)),
                   (Prims.strcat "lemma_" lid.FStar_Ident.str))]
let encode_free_var:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          FStar_Syntax_Syntax.qualifier Prims.list ->
            (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun fv  ->
      fun tt  ->
        fun t_norm  ->
          fun quals  ->
            let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
            let uu____9705 =
              (let uu____9706 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9706) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9705
            then
              let uu____9710 = new_term_constant_and_tok_from_lid env lid in
              match uu____9710 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9722 =
                      let uu____9723 = FStar_Syntax_Subst.compress t_norm in
                      uu____9723.FStar_Syntax_Syntax.n in
                    match uu____9722 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9728) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9745  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9748 -> [] in
                  let d =
                    FStar_SMTEncoding_Term.DeclFun
                      (vname, arg_sorts, FStar_SMTEncoding_Term.Term_sort,
                        (Some
                           "Uninterpreted function symbol for impure function")) in
                  let dd =
                    FStar_SMTEncoding_Term.DeclFun
                      (vtok, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Uninterpreted name for impure function")) in
                  ([d; dd], env1)
            else
              (let uu____9757 = prims.is lid in
               if uu____9757
               then
                 let vname = varops.new_fvar lid in
                 let uu____9762 = prims.mk lid vname in
                 match uu____9762 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9777 =
                    let uu____9783 = curried_arrow_formals_comp t_norm in
                    match uu____9783 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9794 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9794
                          then
                            let uu____9795 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___148_9796 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___148_9796.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___148_9796.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___148_9796.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___148_9796.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___148_9796.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___148_9796.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___148_9796.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___148_9796.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___148_9796.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___148_9796.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___148_9796.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___148_9796.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___148_9796.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___148_9796.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___148_9796.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___148_9796.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___148_9796.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___148_9796.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___148_9796.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___148_9796.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___148_9796.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___148_9796.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___148_9796.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9795
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9803 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9803)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9777 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9830 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____9830 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9843 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___118_9867  ->
                                     match uu___118_9867 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9870 =
                                           FStar_Util.prefix vars in
                                         (match uu____9870 with
                                          | (uu____9881,(xxsym,uu____9883))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____9893 =
                                                let uu____9894 =
                                                  let uu____9898 =
                                                    let uu____9899 =
                                                      let uu____9905 =
                                                        let uu____9906 =
                                                          let uu____9909 =
                                                            let uu____9910 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____9910 in
                                                          (vapp, uu____9909) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9906 in
                                                      ([[vapp]], vars,
                                                        uu____9905) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9899 in
                                                  (uu____9898,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9894 in
                                              [uu____9893])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____9921 =
                                           FStar_Util.prefix vars in
                                         (match uu____9921 with
                                          | (uu____9932,(xxsym,uu____9934))
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
                                              let uu____9948 =
                                                let uu____9949 =
                                                  let uu____9953 =
                                                    let uu____9954 =
                                                      let uu____9960 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____9960) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9954 in
                                                  (uu____9953,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9949 in
                                              [uu____9948])
                                     | uu____9969 -> [])) in
                           let uu____9970 = encode_binders None formals env1 in
                           (match uu____9970 with
                            | (vars,guards,env',decls1,uu____9986) ->
                                let uu____9993 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____9998 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____9998, decls1)
                                  | Some p ->
                                      let uu____10000 = encode_formula p env' in
                                      (match uu____10000 with
                                       | (g,ds) ->
                                           let uu____10007 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10007,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____9993 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10016 =
                                         let uu____10020 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10020) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10016 in
                                     let uu____10025 =
                                       let vname_decl =
                                         let uu____10030 =
                                           let uu____10036 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10041  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10036,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10030 in
                                       let uu____10046 =
                                         let env2 =
                                           let uu___149_10050 = env1 in
                                           {
                                             bindings =
                                               (uu___149_10050.bindings);
                                             depth = (uu___149_10050.depth);
                                             tcenv = (uu___149_10050.tcenv);
                                             warn = (uu___149_10050.warn);
                                             cache = (uu___149_10050.cache);
                                             nolabels =
                                               (uu___149_10050.nolabels);
                                             use_fuel_instrumented_version =
                                               (uu___149_10050.use_fuel_instrumented_version);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___149_10050.current_module_name)
                                           } in
                                         let uu____10051 =
                                           let uu____10052 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10052 in
                                         if uu____10051
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10046 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10062::uu____10063 ->
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
                                                   let uu____10086 =
                                                     let uu____10092 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10092) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10086 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10106 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10108 =
                                             match formals with
                                             | [] ->
                                                 let uu____10117 =
                                                   let uu____10118 =
                                                     let uu____10120 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10120 in
                                                   push_free_var env1 lid
                                                     vname uu____10118 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10117)
                                             | uu____10123 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10128 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10128 in
                                                 let name_tok_corr =
                                                   let uu____10130 =
                                                     let uu____10134 =
                                                       let uu____10135 =
                                                         let uu____10141 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10141) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10135 in
                                                     (uu____10134,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10130 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10108 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10025 with
                                      | (decls2,env2) ->
                                          let uu____10165 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10170 =
                                              encode_term res_t1 env' in
                                            match uu____10170 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10178 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10178,
                                                  decls) in
                                          (match uu____10165 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10186 =
                                                   let uu____10190 =
                                                     let uu____10191 =
                                                       let uu____10197 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10197) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10191 in
                                                   (uu____10190,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10186 in
                                               let freshness =
                                                 let uu____10206 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10206
                                                 then
                                                   let uu____10209 =
                                                     let uu____10210 =
                                                       let uu____10216 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10222 =
                                                         varops.next_id () in
                                                       (vname, uu____10216,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10222) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10210 in
                                                   let uu____10224 =
                                                     let uu____10226 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10226] in
                                                   uu____10209 :: uu____10224
                                                 else [] in
                                               let g =
                                                 let uu____10230 =
                                                   let uu____10232 =
                                                     let uu____10234 =
                                                       let uu____10236 =
                                                         let uu____10238 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10238 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10236 in
                                                     FStar_List.append decls3
                                                       uu____10234 in
                                                   FStar_List.append decls2
                                                     uu____10232 in
                                                 FStar_List.append decls11
                                                   uu____10230 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term Prims.option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10260 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10260 with
          | None  ->
              let uu____10287 = encode_free_var env x t t_norm [] in
              (match uu____10287 with
               | (decls,env1) ->
                   let uu____10302 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10302 with
                    | (n1,x',uu____10323) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10339) -> ((n1, x1), [], env)
let encode_top_level_val:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.qualifier Prims.list ->
          (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun lid  ->
      fun t  ->
        fun quals  ->
          let tt = norm env t in
          let uu____10378 = encode_free_var env lid t tt quals in
          match uu____10378 with
          | (decls,env1) ->
              let uu____10389 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10389
              then
                let uu____10393 =
                  let uu____10395 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10395 in
                (uu____10393, env1)
              else (decls, env1)
let encode_top_level_vals:
  env_t ->
    FStar_Syntax_Syntax.letbinding Prims.list ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun bindings  ->
      fun quals  ->
        FStar_All.pipe_right bindings
          (FStar_List.fold_left
             (fun uu____10423  ->
                fun lb  ->
                  match uu____10423 with
                  | (decls,env1) ->
                      let uu____10435 =
                        let uu____10439 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10439
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10435 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10453 = FStar_Syntax_Util.head_and_args t in
    match uu____10453 with
    | (hd1,args) ->
        let uu____10479 =
          let uu____10480 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10480.FStar_Syntax_Syntax.n in
        (match uu____10479 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10484,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10497 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10512  ->
      fun quals  ->
        match uu____10512 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10561 = FStar_Util.first_N nbinders formals in
              match uu____10561 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10601  ->
                         fun uu____10602  ->
                           match (uu____10601, uu____10602) with
                           | ((formal,uu____10612),(binder,uu____10614)) ->
                               let uu____10619 =
                                 let uu____10624 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10624) in
                               FStar_Syntax_Syntax.NT uu____10619) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10629 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10643  ->
                              match uu____10643 with
                              | (x,i) ->
                                  let uu____10650 =
                                    let uu___150_10651 = x in
                                    let uu____10652 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___150_10651.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___150_10651.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10652
                                    } in
                                  (uu____10650, i))) in
                    FStar_All.pipe_right uu____10629
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10664 =
                      let uu____10666 =
                        let uu____10667 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10667.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10666 in
                    let uu____10671 =
                      let uu____10672 = FStar_Syntax_Subst.compress body in
                      let uu____10673 =
                        let uu____10674 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10674 in
                      FStar_Syntax_Syntax.extend_app_n uu____10672
                        uu____10673 in
                    uu____10671 uu____10664 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10716 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10716
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___151_10717 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___151_10717.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___151_10717.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___151_10717.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___151_10717.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___151_10717.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___151_10717.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___151_10717.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___151_10717.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___151_10717.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___151_10717.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___151_10717.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___151_10717.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___151_10717.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___151_10717.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___151_10717.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___151_10717.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___151_10717.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___151_10717.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___151_10717.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___151_10717.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___151_10717.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___151_10717.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___151_10717.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10738 = FStar_Syntax_Util.abs_formals e in
                match uu____10738 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10787::uu____10788 ->
                         let uu____10796 =
                           let uu____10797 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10797.FStar_Syntax_Syntax.n in
                         (match uu____10796 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10824 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10824 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10850 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10850
                                   then
                                     let uu____10868 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____10868 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____10914  ->
                                                   fun uu____10915  ->
                                                     match (uu____10914,
                                                             uu____10915)
                                                     with
                                                     | ((x,uu____10925),
                                                        (b,uu____10927)) ->
                                                         let uu____10932 =
                                                           let uu____10937 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____10937) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____10932)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____10939 =
                                            let uu____10950 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____10950) in
                                          (uu____10939, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____10985 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____10985 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11037) ->
                              let uu____11042 =
                                let uu____11053 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11053 in
                              (uu____11042, true)
                          | uu____11086 when Prims.op_Negation norm1 ->
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
                          | uu____11088 ->
                              let uu____11089 =
                                let uu____11090 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11091 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11090
                                  uu____11091 in
                              failwith uu____11089)
                     | uu____11104 ->
                         let uu____11105 =
                           let uu____11106 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11106.FStar_Syntax_Syntax.n in
                         (match uu____11105 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11133 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11133 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11151 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11151 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11199 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11227 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11227
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11234 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11275  ->
                            fun lb  ->
                              match uu____11275 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11326 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11326
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11329 =
                                      let uu____11337 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11337
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11329 with
                                    | (tok,decl,env2) ->
                                        let uu____11362 =
                                          let uu____11369 =
                                            let uu____11375 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11375, tok) in
                                          uu____11369 :: toks in
                                        (uu____11362, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11234 with
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
                        | uu____11477 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11482 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11482 vars)
                            else
                              (let uu____11484 =
                                 let uu____11488 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11488) in
                               FStar_SMTEncoding_Util.mkApp uu____11484) in
                      let uu____11493 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___119_11495  ->
                                 match uu___119_11495 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11496 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11499 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11499))) in
                      if uu____11493
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11519;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11521;
                                FStar_Syntax_Syntax.lbeff = uu____11522;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11563 =
                                 let uu____11567 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11567 with
                                 | (tcenv',uu____11578,e_t) ->
                                     let uu____11582 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11589 -> failwith "Impossible" in
                                     (match uu____11582 with
                                      | (e1,t_norm1) ->
                                          ((let uu___154_11598 = env1 in
                                            {
                                              bindings =
                                                (uu___154_11598.bindings);
                                              depth = (uu___154_11598.depth);
                                              tcenv = tcenv';
                                              warn = (uu___154_11598.warn);
                                              cache = (uu___154_11598.cache);
                                              nolabels =
                                                (uu___154_11598.nolabels);
                                              use_fuel_instrumented_version =
                                                (uu___154_11598.use_fuel_instrumented_version);
                                              encode_non_total_function_typ =
                                                (uu___154_11598.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___154_11598.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11563 with
                                | (env',e1,t_norm1) ->
                                    let uu____11605 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11605 with
                                     | ((binders,body,uu____11617,uu____11618),curry)
                                         ->
                                         ((let uu____11625 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11625
                                           then
                                             let uu____11626 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11627 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11626 uu____11627
                                           else ());
                                          (let uu____11629 =
                                             encode_binders None binders env' in
                                           match uu____11629 with
                                           | (vars,guards,env'1,binder_decls,uu____11645)
                                               ->
                                               let body1 =
                                                 let uu____11653 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11653
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11656 =
                                                 let uu____11661 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11661
                                                 then
                                                   let uu____11667 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11668 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11667, uu____11668)
                                                 else
                                                   (let uu____11674 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11674)) in
                                               (match uu____11656 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11688 =
                                                        let uu____11692 =
                                                          let uu____11693 =
                                                            let uu____11699 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11699) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11693 in
                                                        let uu____11705 =
                                                          let uu____11707 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11707 in
                                                        (uu____11692,
                                                          uu____11705,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11688 in
                                                    let uu____11709 =
                                                      let uu____11711 =
                                                        let uu____11713 =
                                                          let uu____11715 =
                                                            let uu____11717 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11717 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11715 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11713 in
                                                      FStar_List.append
                                                        decls1 uu____11711 in
                                                    (uu____11709, env1))))))
                           | uu____11720 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11739 = varops.fresh "fuel" in
                             (uu____11739, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let s_fuel_tm =
                             FStar_SMTEncoding_Util.mkApp
                               ("SFuel", [fuel_tm]) in
                           let env0 = env1 in
                           let uu____11744 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11783  ->
                                     fun uu____11784  ->
                                       match (uu____11783, uu____11784) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____11866 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____11866 in
                                           let gtok =
                                             let uu____11868 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____11868 in
                                           let env3 =
                                             let uu____11870 =
                                               let uu____11872 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [s_fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____11872 in
                                             push_free_var env2 flid gtok
                                               uu____11870 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11744 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____11958
                                 t_norm uu____11960 =
                                 match (uu____11958, uu____11960) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____11987;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____11988;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12005 =
                                       let uu____12009 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12009 with
                                       | (tcenv',uu____12024,e_t) ->
                                           let uu____12028 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12035 ->
                                                 failwith "Impossible" in
                                           (match uu____12028 with
                                            | (e1,t_norm1) ->
                                                ((let uu___155_12044 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___155_12044.bindings);
                                                    depth =
                                                      (uu___155_12044.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___155_12044.warn);
                                                    cache =
                                                      (uu___155_12044.cache);
                                                    nolabels =
                                                      (uu___155_12044.nolabels);
                                                    use_fuel_instrumented_version
                                                      =
                                                      (uu___155_12044.use_fuel_instrumented_version);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___155_12044.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___155_12044.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12005 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12054 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12054
                                            then
                                              let uu____12055 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12056 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12057 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12055 uu____12056
                                                uu____12057
                                            else ());
                                           (let uu____12059 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12059 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12081 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12081
                                                  then
                                                    let uu____12082 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12083 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12084 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12085 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12082 uu____12083
                                                      uu____12084 uu____12085
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12089 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12089 with
                                                  | (vars,guards,env'1,binder_decls,uu____12107)
                                                      ->
                                                      let decl_g =
                                                        let uu____12115 =
                                                          let uu____12121 =
                                                            let uu____12123 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12123 in
                                                          (g, uu____12121,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12115 in
                                                      let env02 =
                                                        push_zfuel_name env01
                                                          flid g in
                                                      let decl_g_tok =
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          (gtok, [],
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Token for fuel-instrumented partial applications")) in
                                                      let vars_tm =
                                                        FStar_List.map
                                                          FStar_SMTEncoding_Util.mkFreeV
                                                          vars in
                                                      let app =
                                                        let uu____12138 =
                                                          let uu____12142 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12142) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12138 in
                                                      let gss_app =
                                                        let uu____12148 =
                                                          let uu____12152 =
                                                            let uu____12154 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [s_fuel_tm]) in
                                                            uu____12154 ::
                                                              vars_tm in
                                                          (g, uu____12152) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12148 in
                                                      let gmax =
                                                        let uu____12158 =
                                                          let uu____12162 =
                                                            let uu____12164 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12164 ::
                                                              vars_tm in
                                                          (g, uu____12162) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12158 in
                                                      let body1 =
                                                        let uu____12168 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12168
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12170 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12170 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12181
                                                               =
                                                               let uu____12185
                                                                 =
                                                                 let uu____12186
                                                                   =
                                                                   let uu____12194
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gss_app,
                                                                    body_tm) in
                                                                   ([
                                                                    [gss_app]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12194) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12186 in
                                                               let uu____12205
                                                                 =
                                                                 let uu____12207
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12207 in
                                                               (uu____12185,
                                                                 uu____12205,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12181 in
                                                           let eqn_f =
                                                             let uu____12210
                                                               =
                                                               let uu____12214
                                                                 =
                                                                 let uu____12215
                                                                   =
                                                                   let uu____12221
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12221) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12215 in
                                                               (uu____12214,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12210 in
                                                           let eqn_g' =
                                                             let gs_app =
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 (g,
                                                                   (s_fuel_tm
                                                                   ::
                                                                   vars_tm)) in
                                                             let g_app =
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 (g, (fuel_tm
                                                                   ::
                                                                   vars_tm)) in
                                                             let uu____12233
                                                               =
                                                               let uu____12237
                                                                 =
                                                                 let uu____12238
                                                                   =
                                                                   let uu____12244
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gss_app,
                                                                    g_app) in
                                                                   ([
                                                                    [gs_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12244) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12238 in
                                                               (uu____12237,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12233 in
                                                           let uu____12255 =
                                                             let uu____12260
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12260
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12277)
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
                                                                    let uu____12292
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12292
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12295
                                                                    =
                                                                    let uu____12299
                                                                    =
                                                                    let uu____12300
                                                                    =
                                                                    let uu____12306
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12306) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12300 in
                                                                    (uu____12299,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12295 in
                                                                 let uu____12317
                                                                   =
                                                                   let uu____12321
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12321
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12329
                                                                    =
                                                                    let uu____12331
                                                                    =
                                                                    let uu____12332
                                                                    =
                                                                    let uu____12336
                                                                    =
                                                                    let uu____12337
                                                                    =
                                                                    let uu____12343
                                                                    =
                                                                    let uu____12344
                                                                    =
                                                                    let uu____12347
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12347,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12344 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12343) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12337 in
                                                                    (uu____12336,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12332 in
                                                                    [uu____12331] in
                                                                    (d3,
                                                                    uu____12329) in
                                                                 (match uu____12317
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12255
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
                               let uu____12382 =
                                 let uu____12389 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12425  ->
                                      fun uu____12426  ->
                                        match (uu____12425, uu____12426) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12512 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12512 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12389 in
                               (match uu____12382 with
                                | (decls2,eqns,env01) ->
                                    let uu____12552 =
                                      let isDeclFun uu___120_12560 =
                                        match uu___120_12560 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12561 -> true
                                        | uu____12567 -> false in
                                      let uu____12568 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12568
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12552 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12595 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12595
                     (FStar_String.concat " and ") in
                 let decl =
                   FStar_SMTEncoding_Term.Caption
                     (Prims.strcat "let rec unencodeable: Skipping: " msg) in
                 ([decl], env))
let rec encode_sigelt:
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      let nm =
        let uu____12628 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12628 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12631 = encode_sigelt' env se in
      match uu____12631 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12641 =
                  let uu____12642 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12642 in
                [uu____12641]
            | uu____12643 ->
                let uu____12644 =
                  let uu____12646 =
                    let uu____12647 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12647 in
                  uu____12646 :: g in
                let uu____12648 =
                  let uu____12650 =
                    let uu____12651 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12651 in
                  [uu____12650] in
                FStar_List.append uu____12644 uu____12648 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12659 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12668 =
            let uu____12669 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12669 Prims.op_Negation in
          if uu____12668
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12689 ->
                   let uu____12690 =
                     let uu____12693 =
                       let uu____12694 =
                         let uu____12709 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12709) in
                       FStar_Syntax_Syntax.Tm_abs uu____12694 in
                     FStar_Syntax_Syntax.mk uu____12693 in
                   uu____12690 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12762 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12762 with
               | (aname,atok,env2) ->
                   let uu____12772 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12772 with
                    | (formals,uu____12782) ->
                        let uu____12789 =
                          let uu____12792 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12792 env2 in
                        (match uu____12789 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12800 =
                                 let uu____12801 =
                                   let uu____12807 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12815  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12807,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12801 in
                               [uu____12800;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12822 =
                               let aux uu____12851 uu____12852 =
                                 match (uu____12851, uu____12852) with
                                 | ((bv,uu____12879),(env3,acc_sorts,acc)) ->
                                     let uu____12900 = gen_term_var env3 bv in
                                     (match uu____12900 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12822 with
                              | (uu____12938,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____12952 =
                                      let uu____12956 =
                                        let uu____12957 =
                                          let uu____12963 =
                                            let uu____12964 =
                                              let uu____12967 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____12967) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12964 in
                                          ([[app]], xs_sorts, uu____12963) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12957 in
                                      (uu____12956, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12952 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____12979 =
                                      let uu____12983 =
                                        let uu____12984 =
                                          let uu____12990 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____12990) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12984 in
                                      (uu____12983,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12979 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13000 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13000 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13016,uu____13017)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13018 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13018 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13029,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13034 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___121_13036  ->
                      match uu___121_13036 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13039 -> false)) in
            Prims.op_Negation uu____13034 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13045 = encode_top_level_val env fv t quals in
             match uu____13045 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13057 =
                   let uu____13059 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13059 in
                 (uu____13057, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13064 = encode_formula f env in
          (match uu____13064 with
           | (f1,decls) ->
               let g =
                 let uu____13073 =
                   let uu____13074 =
                     let uu____13078 =
                       let uu____13080 =
                         let uu____13081 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13081 in
                       Some uu____13080 in
                     let uu____13082 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13078, uu____13082) in
                   FStar_SMTEncoding_Util.mkAssume uu____13074 in
                 [uu____13073] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13086,uu____13087) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13093 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13100 =
                       let uu____13105 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13105.FStar_Syntax_Syntax.fv_name in
                     uu____13100.FStar_Syntax_Syntax.v in
                   let uu____13109 =
                     let uu____13110 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13110 in
                   if uu____13109
                   then
                     let val_decl =
                       let uu___156_13125 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___156_13125.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___156_13125.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___156_13125.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13129 = encode_sigelt' env1 val_decl in
                     match uu____13129 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13093 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13146,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13148;
                          FStar_Syntax_Syntax.lbtyp = uu____13149;
                          FStar_Syntax_Syntax.lbeff = uu____13150;
                          FStar_Syntax_Syntax.lbdef = uu____13151;_}::[]),uu____13152,uu____13153)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13167 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13167 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13190 =
                   let uu____13192 =
                     let uu____13193 =
                       let uu____13197 =
                         let uu____13198 =
                           let uu____13204 =
                             let uu____13205 =
                               let uu____13208 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13208) in
                             FStar_SMTEncoding_Util.mkEq uu____13205 in
                           ([[b2t_x]], [xx], uu____13204) in
                         FStar_SMTEncoding_Util.mkForall uu____13198 in
                       (uu____13197, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13193 in
                   [uu____13192] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13190 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13225,uu____13226,uu____13227)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13233  ->
                  match uu___122_13233 with
                  | FStar_Syntax_Syntax.Discriminator uu____13234 -> true
                  | uu____13235 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13237,lids,uu____13239) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13246 =
                     let uu____13247 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13247.FStar_Ident.idText in
                   uu____13246 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___123_13249  ->
                     match uu___123_13249 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13250 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13253,uu____13254)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___124_13264  ->
                  match uu___124_13264 with
                  | FStar_Syntax_Syntax.Projector uu____13265 -> true
                  | uu____13268 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13275 = try_lookup_free_var env l in
          (match uu____13275 with
           | Some uu____13279 -> ([], env)
           | None  ->
               let se1 =
                 let uu___157_13282 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___157_13282.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___157_13282.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13288,uu____13289) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13301) ->
          let uu____13306 = encode_sigelts env ses in
          (match uu____13306 with
           | (g,env1) ->
               let uu____13316 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___125_13326  ->
                         match uu___125_13326 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13327;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13328;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13329;_}
                             -> false
                         | uu____13331 -> true)) in
               (match uu____13316 with
                | (g',inversions) ->
                    let uu____13340 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___126_13350  ->
                              match uu___126_13350 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13351 ->
                                  true
                              | uu____13357 -> false)) in
                    (match uu____13340 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13368,tps,k,uu____13371,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___127_13381  ->
                    match uu___127_13381 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13382 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13389 = c in
              match uu____13389 with
              | (name,args,uu____13393,uu____13394,uu____13395) ->
                  let uu____13398 =
                    let uu____13399 =
                      let uu____13405 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13412  ->
                                match uu____13412 with
                                | (uu____13416,sort,uu____13418) -> sort)) in
                      (name, uu____13405, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13399 in
                  [uu____13398]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13436 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13439 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13439 FStar_Option.isNone)) in
            if uu____13436
            then []
            else
              (let uu____13456 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13456 with
               | (xxsym,xx) ->
                   let uu____13462 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13473  ->
                             fun l  ->
                               match uu____13473 with
                               | (out,decls) ->
                                   let uu____13485 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13485 with
                                    | (uu____13491,data_t) ->
                                        let uu____13493 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13493 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13522 =
                                                 let uu____13523 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13523.FStar_Syntax_Syntax.n in
                                               match uu____13522 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13531,indices) ->
                                                   indices
                                               | uu____13547 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13559  ->
                                                         match uu____13559
                                                         with
                                                         | (x,uu____13563) ->
                                                             let uu____13564
                                                               =
                                                               let uu____13565
                                                                 =
                                                                 let uu____13569
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13569,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13565 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13564)
                                                    env) in
                                             let uu____13571 =
                                               encode_args indices env1 in
                                             (match uu____13571 with
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
                                                      let uu____13591 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13599
                                                                 =
                                                                 let uu____13602
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13602,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13599)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13591
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13604 =
                                                      let uu____13605 =
                                                        let uu____13608 =
                                                          let uu____13609 =
                                                            let uu____13612 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13612,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13609 in
                                                        (out, uu____13608) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13605 in
                                                    (uu____13604,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13462 with
                    | (data_ax,decls) ->
                        let uu____13620 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13620 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13631 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13631 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13634 =
                                 let uu____13638 =
                                   let uu____13639 =
                                     let uu____13645 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13653 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13645,
                                       uu____13653) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13639 in
                                 let uu____13661 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13638, (Some "inversion axiom"),
                                   uu____13661) in
                               FStar_SMTEncoding_Util.mkAssume uu____13634 in
                             let pattern_guarded_inversion =
                               let uu____13665 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13665
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13673 =
                                   let uu____13674 =
                                     let uu____13678 =
                                       let uu____13679 =
                                         let uu____13685 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13693 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13685, uu____13693) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13679 in
                                     let uu____13701 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13678, (Some "inversion axiom"),
                                       uu____13701) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13674 in
                                 [uu____13673]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13704 =
            let uu____13712 =
              let uu____13713 = FStar_Syntax_Subst.compress k in
              uu____13713.FStar_Syntax_Syntax.n in
            match uu____13712 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13742 -> (tps, k) in
          (match uu____13704 with
           | (formals,res) ->
               let uu____13757 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13757 with
                | (formals1,res1) ->
                    let uu____13764 = encode_binders None formals1 env in
                    (match uu____13764 with
                     | (vars,guards,env',binder_decls,uu____13779) ->
                         let uu____13786 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13786 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13799 =
                                  let uu____13803 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13803) in
                                FStar_SMTEncoding_Util.mkApp uu____13799 in
                              let uu____13808 =
                                let tname_decl =
                                  let uu____13814 =
                                    let uu____13815 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13830  ->
                                              match uu____13830 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13838 = varops.next_id () in
                                    (tname, uu____13815,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13838, false) in
                                  constructor_or_logic_type_decl uu____13814 in
                                let uu____13843 =
                                  match vars with
                                  | [] ->
                                      let uu____13850 =
                                        let uu____13851 =
                                          let uu____13853 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13853 in
                                        push_free_var env1 t tname
                                          uu____13851 in
                                      ([], uu____13850)
                                  | uu____13857 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13863 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13863 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13872 =
                                          let uu____13876 =
                                            let uu____13877 =
                                              let uu____13885 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13885) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13877 in
                                          (uu____13876,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13872 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13843 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13808 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13908 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____13908 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13922 =
                                               let uu____13923 =
                                                 let uu____13927 =
                                                   let uu____13928 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13928 in
                                                 (uu____13927,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13923 in
                                             [uu____13922]
                                           else [] in
                                         let uu____13931 =
                                           let uu____13933 =
                                             let uu____13935 =
                                               let uu____13936 =
                                                 let uu____13940 =
                                                   let uu____13941 =
                                                     let uu____13947 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____13947) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____13941 in
                                                 (uu____13940, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13936 in
                                             [uu____13935] in
                                           FStar_List.append karr uu____13933 in
                                         FStar_List.append decls1 uu____13931 in
                                   let aux =
                                     let uu____13956 =
                                       let uu____13958 =
                                         inversion_axioms tapp vars in
                                       let uu____13960 =
                                         let uu____13962 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____13962] in
                                       FStar_List.append uu____13958
                                         uu____13960 in
                                     FStar_List.append kindingAx uu____13956 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13967,uu____13968,uu____13969,uu____13970,uu____13971)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13976,t,uu____13978,n_tps,uu____13980) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____13985 = new_term_constant_and_tok_from_lid env d in
          (match uu____13985 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____13996 = FStar_Syntax_Util.arrow_formals t in
               (match uu____13996 with
                | (formals,t_res) ->
                    let uu____14018 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14018 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14027 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14027 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14065 =
                                            mk_term_projector_name d x in
                                          (uu____14065,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14067 =
                                  let uu____14077 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14077, true) in
                                FStar_All.pipe_right uu____14067
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
                              let uu____14099 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14099 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14107::uu____14108 ->
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
                                         let uu____14133 =
                                           let uu____14139 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14139) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14133
                                     | uu____14152 -> tok_typing in
                                   let uu____14157 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14157 with
                                    | (vars',guards',env'',decls_formals,uu____14172)
                                        ->
                                        let uu____14179 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14179 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14198 ->
                                                   let uu____14202 =
                                                     let uu____14203 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14203 in
                                                   [uu____14202] in
                                             let encode_elim uu____14210 =
                                               let uu____14211 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14211 with
                                               | (head1,args) ->
                                                   let uu____14240 =
                                                     let uu____14241 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14241.FStar_Syntax_Syntax.n in
                                                   (match uu____14240 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                      ({
                                                         FStar_Syntax_Syntax.n
                                                           =
                                                           FStar_Syntax_Syntax.Tm_fvar
                                                           fv;
                                                         FStar_Syntax_Syntax.tk
                                                           = _;
                                                         FStar_Syntax_Syntax.pos
                                                           = _;
                                                         FStar_Syntax_Syntax.vars
                                                           = _;_},_)
                                                      |FStar_Syntax_Syntax.Tm_fvar
                                                      fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14259 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14259
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
                                                                 | uu____14285
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14293
                                                                    =
                                                                    let uu____14294
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14294 in
                                                                    if
                                                                    uu____14293
                                                                    then
                                                                    let uu____14301
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14301]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14303
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14316
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14316
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14338
                                                                    =
                                                                    let uu____14342
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14342 in
                                                                    (match uu____14338
                                                                    with
                                                                    | 
                                                                    (uu____14349,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14355
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14355
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14357
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14357
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
                                                             (match uu____14303
                                                              with
                                                              | (uu____14365,arg_vars,elim_eqns_or_guards,uu____14368)
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
                                                                    (Some
                                                                    s_fuel_tm)
                                                                    dapp1 ty in
                                                                  let arg_binders
                                                                    =
                                                                    FStar_List.map
                                                                    FStar_SMTEncoding_Term.fv_of_term
                                                                    arg_vars1 in
                                                                  let typing_inversion
                                                                    =
                                                                    let uu____14387
                                                                    =
                                                                    let uu____14391
                                                                    =
                                                                    let uu____14392
                                                                    =
                                                                    let uu____14398
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14404
                                                                    =
                                                                    let uu____14405
                                                                    =
                                                                    let uu____14408
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14408) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14405 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14398,
                                                                    uu____14404) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14392 in
                                                                    (uu____14391,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14387 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14421
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14421,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14423
                                                                    =
                                                                    let uu____14427
                                                                    =
                                                                    let uu____14428
                                                                    =
                                                                    let uu____14434
                                                                    =
                                                                    let uu____14437
                                                                    =
                                                                    let uu____14439
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14439] in
                                                                    [uu____14437] in
                                                                    let uu____14442
                                                                    =
                                                                    let uu____14443
                                                                    =
                                                                    let uu____14446
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14447
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14446,
                                                                    uu____14447) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14443 in
                                                                    (uu____14434,
                                                                    [x],
                                                                    uu____14442) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14428 in
                                                                    let uu____14457
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14427,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14457) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14423
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14462
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
                                                                    (let uu____14477
                                                                    =
                                                                    let uu____14478
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14478
                                                                    dapp1 in
                                                                    [uu____14477]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14462
                                                                    FStar_List.flatten in
                                                                    let uu____14482
                                                                    =
                                                                    let uu____14486
                                                                    =
                                                                    let uu____14487
                                                                    =
                                                                    let uu____14493
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14499
                                                                    =
                                                                    let uu____14500
                                                                    =
                                                                    let uu____14503
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14503) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14500 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14493,
                                                                    uu____14499) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14487 in
                                                                    (uu____14486,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14482) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14513 ->
                                                        ((let uu____14515 =
                                                            let uu____14516 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14517 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14516
                                                              uu____14517 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14515);
                                                         ([], []))) in
                                             let uu____14520 = encode_elim () in
                                             (match uu____14520 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14532 =
                                                      let uu____14534 =
                                                        let uu____14536 =
                                                          let uu____14538 =
                                                            let uu____14540 =
                                                              let uu____14541
                                                                =
                                                                let uu____14547
                                                                  =
                                                                  let uu____14549
                                                                    =
                                                                    let uu____14550
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14550 in
                                                                  Some
                                                                    uu____14549 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14547) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14541 in
                                                            [uu____14540] in
                                                          let uu____14553 =
                                                            let uu____14555 =
                                                              let uu____14557
                                                                =
                                                                let uu____14559
                                                                  =
                                                                  let uu____14561
                                                                    =
                                                                    let uu____14563
                                                                    =
                                                                    let uu____14565
                                                                    =
                                                                    let uu____14566
                                                                    =
                                                                    let uu____14570
                                                                    =
                                                                    let uu____14571
                                                                    =
                                                                    let uu____14577
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14577) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14571 in
                                                                    (uu____14570,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14566 in
                                                                    let uu____14584
                                                                    =
                                                                    let uu____14586
                                                                    =
                                                                    let uu____14587
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    let uu____14592
                                                                    =
                                                                    let uu____14598
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14604
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14598,
                                                                    uu____14604) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14592 in
                                                                    (uu____14591,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14587 in
                                                                    [uu____14586] in
                                                                    uu____14565
                                                                    ::
                                                                    uu____14584 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14563 in
                                                                  FStar_List.append
                                                                    uu____14561
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14559 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14557 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14555 in
                                                          FStar_List.append
                                                            uu____14538
                                                            uu____14553 in
                                                        FStar_List.append
                                                          decls3 uu____14536 in
                                                      FStar_List.append
                                                        decls2 uu____14534 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14532 in
                                                  ((FStar_List.append
                                                      datacons g), env1)))))))))
and encode_sigelts:
  env_t ->
    FStar_Syntax_Syntax.sigelt Prims.list ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun ses  ->
      FStar_All.pipe_right ses
        (FStar_List.fold_left
           (fun uu____14625  ->
              fun se  ->
                match uu____14625 with
                | (g,env1) ->
                    let uu____14637 = encode_sigelt env1 se in
                    (match uu____14637 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14673 =
        match uu____14673 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14691 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14696 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14696
                   then
                     let uu____14697 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14698 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14699 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14697 uu____14698 uu____14699
                   else ());
                  (let uu____14701 = encode_term t1 env1 in
                   match uu____14701 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14711 =
                         let uu____14715 =
                           let uu____14716 =
                             let uu____14717 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14717
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14716 in
                         new_term_constant_from_string env1 x uu____14715 in
                       (match uu____14711 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14728 = FStar_Options.log_queries () in
                              if uu____14728
                              then
                                let uu____14730 =
                                  let uu____14731 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14732 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14733 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14731 uu____14732 uu____14733 in
                                Some uu____14730
                              else None in
                            let ax =
                              let a_name = Prims.strcat "binder_" xxsym in
                              FStar_SMTEncoding_Util.mkAssume
                                (t2, (Some a_name), a_name) in
                            let g =
                              FStar_List.append
                                [FStar_SMTEncoding_Term.DeclFun
                                   (xxsym, [],
                                     FStar_SMTEncoding_Term.Term_sort,
                                     caption)]
                                (FStar_List.append decls' [ax]) in
                            ((i + (Prims.parse_int "1")),
                              (FStar_List.append decls g), env'))))
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14744,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14753 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14753 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14772 = encode_sigelt env1 se in
                 (match uu____14772 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14782 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14782 with | (uu____14794,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14839  ->
            match uu____14839 with
            | (l,uu____14846,uu____14847) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14868  ->
            match uu____14868 with
            | (l,uu____14876,uu____14877) ->
                let uu____14882 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____14883 =
                  let uu____14885 =
                    let uu____14886 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14886 in
                  [uu____14885] in
                uu____14882 :: uu____14883)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14897 =
      let uu____14899 =
        let uu____14900 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____14902 =
          let uu____14903 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____14903 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14900;
          nolabels = false;
          use_fuel_instrumented_version = None;
          encode_non_total_function_typ = true;
          current_module_name = uu____14902
        } in
      [uu____14899] in
    FStar_ST.write last_env uu____14897
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____14913 = FStar_ST.read last_env in
      match uu____14913 with
      | [] -> failwith "No env; call init first!"
      | e::uu____14919 ->
          let uu___158_14921 = e in
          let uu____14922 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___158_14921.bindings);
            depth = (uu___158_14921.depth);
            tcenv;
            warn = (uu___158_14921.warn);
            cache = (uu___158_14921.cache);
            nolabels = (uu___158_14921.nolabels);
            use_fuel_instrumented_version =
              (uu___158_14921.use_fuel_instrumented_version);
            encode_non_total_function_typ =
              (uu___158_14921.encode_non_total_function_typ);
            current_module_name = uu____14922
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____14926 = FStar_ST.read last_env in
    match uu____14926 with
    | [] -> failwith "Empty env stack"
    | uu____14931::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____14939  ->
    let uu____14940 = FStar_ST.read last_env in
    match uu____14940 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___159_14951 = hd1 in
          {
            bindings = (uu___159_14951.bindings);
            depth = (uu___159_14951.depth);
            tcenv = (uu___159_14951.tcenv);
            warn = (uu___159_14951.warn);
            cache = refs;
            nolabels = (uu___159_14951.nolabels);
            use_fuel_instrumented_version =
              (uu___159_14951.use_fuel_instrumented_version);
            encode_non_total_function_typ =
              (uu___159_14951.encode_non_total_function_typ);
            current_module_name = (uu___159_14951.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____14957  ->
    let uu____14958 = FStar_ST.read last_env in
    match uu____14958 with
    | [] -> failwith "Popping an empty stack"
    | uu____14963::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____14971  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____14974  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____14977  ->
    let uu____14978 = FStar_ST.read last_env in
    match uu____14978 with
    | hd1::uu____14984::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____14990 -> failwith "Impossible"
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
        | (uu____15039::uu____15040,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___160_15044 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___160_15044.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___160_15044.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___160_15044.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15045 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15056 =
        let uu____15058 =
          let uu____15059 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15059 in
        let uu____15060 = open_fact_db_tags env in uu____15058 :: uu____15060 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15056
let encode_top_level_facts:
  env_t ->
    FStar_Syntax_Syntax.sigelt ->
      (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun se  ->
      let fact_db_ids =
        FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
          (FStar_List.collect (fact_dbs_for_lid env)) in
      let uu____15075 = encode_sigelt env se in
      match uu____15075 with
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
        let uu____15100 = FStar_Options.log_queries () in
        if uu____15100
        then
          let uu____15102 =
            let uu____15103 =
              let uu____15104 =
                let uu____15105 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15105 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15104 in
            FStar_SMTEncoding_Term.Caption uu____15103 in
          uu____15102 :: decls
        else decls in
      let env =
        let uu____15112 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15112 tcenv in
      let uu____15113 = encode_top_level_facts env se in
      match uu____15113 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15122 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15122))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15133 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15133
       then
         let uu____15134 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15134
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15155  ->
                 fun se  ->
                   match uu____15155 with
                   | (g,env2) ->
                       let uu____15167 = encode_top_level_facts env2 se in
                       (match uu____15167 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15180 =
         encode_signature
           (let uu___161_15184 = env in
            {
              bindings = (uu___161_15184.bindings);
              depth = (uu___161_15184.depth);
              tcenv = (uu___161_15184.tcenv);
              warn = false;
              cache = (uu___161_15184.cache);
              nolabels = (uu___161_15184.nolabels);
              use_fuel_instrumented_version =
                (uu___161_15184.use_fuel_instrumented_version);
              encode_non_total_function_typ =
                (uu___161_15184.encode_non_total_function_typ);
              current_module_name = (uu___161_15184.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15180 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15196 = FStar_Options.log_queries () in
             if uu____15196
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___162_15201 = env1 in
               {
                 bindings = (uu___162_15201.bindings);
                 depth = (uu___162_15201.depth);
                 tcenv = (uu___162_15201.tcenv);
                 warn = true;
                 cache = (uu___162_15201.cache);
                 nolabels = (uu___162_15201.nolabels);
                 use_fuel_instrumented_version =
                   (uu___162_15201.use_fuel_instrumented_version);
                 encode_non_total_function_typ =
                   (uu___162_15201.encode_non_total_function_typ);
                 current_module_name = (uu___162_15201.current_module_name)
               });
            (let uu____15203 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15203
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) Prims.option ->
    FStar_TypeChecker_Env.env ->
      FStar_Syntax_Syntax.term ->
        (FStar_SMTEncoding_Term.decl Prims.list*
          FStar_SMTEncoding_ErrorReporting.label Prims.list*
          FStar_SMTEncoding_Term.decl* FStar_SMTEncoding_Term.decl
          Prims.list)
  =
  fun use_env_msg  ->
    fun tcenv  ->
      fun q  ->
        (let uu____15238 =
           let uu____15239 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15239.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15238);
        (let env =
           let uu____15241 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15241 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15248 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15269 = aux rest in
                 (match uu____15269 with
                  | (out,rest1) ->
                      let t =
                        let uu____15287 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15287 with
                        | Some uu____15291 ->
                            let uu____15292 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15292
                              x.FStar_Syntax_Syntax.sort
                        | uu____15293 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15296 =
                        let uu____15298 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___163_15299 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___163_15299.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___163_15299.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15298 :: out in
                      (uu____15296, rest1))
             | uu____15302 -> ([], bindings1) in
           let uu____15306 = aux bindings in
           match uu____15306 with
           | (closing,bindings1) ->
               let uu____15320 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15320, bindings1) in
         match uu____15248 with
         | (q1,bindings1) ->
             let uu____15333 =
               let uu____15336 =
                 FStar_List.filter
                   (fun uu___128_15338  ->
                      match uu___128_15338 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15339 ->
                          false
                      | uu____15343 -> true) bindings1 in
               encode_env_bindings env uu____15336 in
             (match uu____15333 with
              | (env_decls,env1) ->
                  ((let uu____15354 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15354
                    then
                      let uu____15355 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15355
                    else ());
                   (let uu____15357 = encode_formula q1 env1 in
                    match uu____15357 with
                    | (phi,qdecls) ->
                        let uu____15369 =
                          let uu____15372 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15372 phi in
                        (match uu____15369 with
                         | (labels,phi1) ->
                             let uu____15382 = encode_labels labels in
                             (match uu____15382 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15403 =
                                      let uu____15407 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15408 =
                                        varops.mk_unique "@query" in
                                      (uu____15407, (Some "query"),
                                        uu____15408) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15403 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15421 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15421 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15423 = encode_formula q env in
       match uu____15423 with
       | (f,uu____15427) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15429) -> true
             | uu____15432 -> false)))