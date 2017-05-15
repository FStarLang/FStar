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
let is_fuel_term: FStar_SMTEncoding_Term.term -> Prims.bool =
  fun t  ->
    match t.FStar_SMTEncoding_Term.tm with
    | FStar_SMTEncoding_Term.FreeV uu____1433 ->
        let uu____1436 =
          let uu____1437 = FStar_SMTEncoding_Term.fv_of_term t in
          FStar_All.pipe_right uu____1437 Prims.fst in
        FStar_Util.starts_with uu____1436 "fuel"
    | FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var "SFuel",_)
      |FStar_SMTEncoding_Term.App (FStar_SMTEncoding_Term.Var "ZFuel",_) ->
        true
    | uu____1442 -> false
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1450 = try_lookup_lid env l in
      match uu____1450 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match (zf_opt, (env.use_fuel_instrumented_version)) with
           | (Some f,Some fuel) -> let uu____1500 = f fuel in Some uu____1500
           | uu____1501 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1511,fuel::[]) when
                         is_fuel_term fuel ->
                         let uu____1514 =
                           let uu____1515 =
                             FStar_SMTEncoding_Util.mkFreeV
                               (name, FStar_SMTEncoding_Term.Term_sort) in
                           FStar_SMTEncoding_Term.mk_ApplyTF uu____1515 fuel in
                         FStar_All.pipe_left (fun _0_30  -> Some _0_30)
                           uu____1514
                     | uu____1517 -> Some t)
                | uu____1518 -> None))
let lookup_free_var env a =
  let uu____1536 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1536 with
  | Some t -> t
  | None  ->
      let uu____1539 =
        let uu____1540 =
          FStar_Syntax_Print.lid_to_string a.FStar_Syntax_Syntax.v in
        FStar_Util.format1 "Name not found: %s" uu____1540 in
      failwith uu____1539
let lookup_free_var_name env a =
  let uu____1557 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1557 with | (x,uu____1566,uu____1567) -> x
let lookup_free_var_sym env a =
  let uu____1595 = lookup_lid env a.FStar_Syntax_Syntax.v in
  match uu____1595 with
  | (name,sym,zf_opt) ->
      (match (zf_opt, (env.use_fuel_instrumented_version)) with
       | (Some mkf,Some fuel) ->
           let uu____1634 =
             let uu____1635 = mkf fuel in
             uu____1635.FStar_SMTEncoding_Term.tm in
           (match uu____1634 with
            | FStar_SMTEncoding_Term.App (g,zf) -> (g, zf)
            | uu____1644 -> failwith "Impossible")
       | uu____1648 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1667 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___110_1676  ->
           match uu___110_1676 with
           | Binding_fvar (uu____1678,nm',tok,uu____1681) when nm = nm' ->
               tok
           | uu____1690 -> None)
let mkForall_fuel' n1 uu____1707 =
  match uu____1707 with
  | (pats,vars,body) ->
      let fallback uu____1723 =
        FStar_SMTEncoding_Util.mkForall (pats, vars, body) in
      let uu____1726 = FStar_Options.unthrottle_inductives () in
      if uu____1726
      then fallback ()
      else
        (let uu____1728 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
         match uu____1728 with
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
                       | uu____1747 -> p)) in
             let pats1 = FStar_List.map add_fuel1 pats in
             let body1 =
               match body.FStar_SMTEncoding_Term.tm with
               | FStar_SMTEncoding_Term.App
                   (FStar_SMTEncoding_Term.Imp ,guard::body'::[]) ->
                   let guard1 =
                     match guard.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App
                         (FStar_SMTEncoding_Term.And ,guards) ->
                         let uu____1761 = add_fuel1 guards in
                         FStar_SMTEncoding_Util.mk_and_l uu____1761
                     | uu____1763 ->
                         let uu____1764 = add_fuel1 [guard] in
                         FStar_All.pipe_right uu____1764 FStar_List.hd in
                   FStar_SMTEncoding_Util.mkImp (guard1, body')
               | uu____1767 -> body in
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
          let uu____1811 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1811 FStar_Option.isNone
      | uu____1824 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1831 =
        let uu____1832 = FStar_Syntax_Util.un_uinst t in
        uu____1832.FStar_Syntax_Syntax.n in
      match uu____1831 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1835,uu____1836,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___111_1865  ->
                  match uu___111_1865 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1866 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1867,uu____1868,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1895 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1895 FStar_Option.isSome
      | uu____1908 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1915 = head_normal env t in
      if uu____1915
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
    let uu____1926 =
      let uu____1927 = FStar_Syntax_Syntax.null_binder t in [uu____1927] in
    let uu____1928 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1926 uu____1928 None
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
                    let uu____1955 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1955
                | s ->
                    let uu____1958 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1958) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___112_1970  ->
    match uu___112_1970 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1971 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1999;
                       FStar_SMTEncoding_Term.rng = uu____2000;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____2014) ->
              let uu____2019 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____2029 -> false) args (FStar_List.rev xs)) in
              if uu____2019 then tok_of_name env f else None
          | (uu____2032,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____2035 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____2037 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____2037)) in
              if uu____2035 then Some t else None
          | uu____2040 -> None in
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
    | uu____2124 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___113_2127  ->
    match uu___113_2127 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2129 =
          let uu____2133 =
            let uu____2135 =
              let uu____2136 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2136 in
            [uu____2135] in
          ("FStar.Char.Char", uu____2133) in
        FStar_SMTEncoding_Util.mkApp uu____2129
    | FStar_Const.Const_int (i,None ) ->
        let uu____2144 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2144
    | FStar_Const.Const_int (i,Some uu____2146) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2155) ->
        let uu____2158 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2158
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2162 =
          let uu____2163 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2163 in
        failwith uu____2162
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2182 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2190 ->
            let uu____2195 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2195
        | uu____2196 ->
            if norm1
            then let uu____2197 = whnf env t1 in aux false uu____2197
            else
              (let uu____2199 =
                 let uu____2200 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2201 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2200 uu____2201 in
               failwith uu____2199) in
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
    | uu____2222 ->
        let uu____2223 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2223)
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
        (let uu____2363 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2363
         then
           let uu____2364 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2364
         else ());
        (let uu____2366 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2402  ->
                   fun b  ->
                     match uu____2402 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2445 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2454 = gen_term_var env1 x in
                           match uu____2454 with
                           | (xxsym,xx,env') ->
                               let uu____2468 =
                                 let uu____2471 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2471 env1 xx in
                               (match uu____2468 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2445 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2366 with
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
          let uu____2559 = encode_term t env in
          match uu____2559 with
          | (t1,decls) ->
              let uu____2566 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2566, decls)
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
          let uu____2574 = encode_term t env in
          match uu____2574 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2583 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2583, decls)
               | Some f ->
                   let uu____2585 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2585, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2592 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2592
       then
         let uu____2593 = FStar_Syntax_Print.tag_of_term t in
         let uu____2594 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2595 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2593 uu____2594
           uu____2595
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2600 =
             let uu____2601 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2602 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2603 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2604 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2601
               uu____2602 uu____2603 uu____2604 in
           failwith uu____2600
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2608 =
             let uu____2609 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2609 in
           failwith uu____2608
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2614) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2644) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2653 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2653, [])
       | FStar_Syntax_Syntax.Tm_type uu____2659 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2662) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2668 = encode_const c in (uu____2668, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2683 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2683 with
            | (binders1,res) ->
                let uu____2690 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2690
                then
                  let uu____2693 = encode_binders None binders1 env in
                  (match uu____2693 with
                   | (vars,guards,env',decls,uu____2708) ->
                       let fsym =
                         let uu____2718 = varops.fresh "f" in
                         (uu____2718, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2721 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___138_2725 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___138_2725.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___138_2725.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___138_2725.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___138_2725.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___138_2725.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___138_2725.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___138_2725.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___138_2725.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___138_2725.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___138_2725.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___138_2725.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___138_2725.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___138_2725.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___138_2725.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___138_2725.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___138_2725.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___138_2725.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___138_2725.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___138_2725.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___138_2725.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___138_2725.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___138_2725.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___138_2725.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2721 with
                        | (pre_opt,res_t) ->
                            let uu____2732 =
                              encode_term_pred None res_t env' app in
                            (match uu____2732 with
                             | (res_pred,decls') ->
                                 let uu____2739 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2746 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2746, [])
                                   | Some pre ->
                                       let uu____2749 =
                                         encode_formula pre env' in
                                       (match uu____2749 with
                                        | (guard,decls0) ->
                                            let uu____2757 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2757, decls0)) in
                                 (match uu____2739 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2765 =
                                          let uu____2771 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2771) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2765 in
                                      let cvars =
                                        let uu____2781 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2781
                                          (FStar_List.filter
                                             (fun uu____2787  ->
                                                match uu____2787 with
                                                | (x,uu____2791) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2802 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2802 with
                                       | Some cache_entry ->
                                           let uu____2807 =
                                             let uu____2808 =
                                               let uu____2812 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2812) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2808 in
                                           (uu____2807,
                                             (use_cache_entry cache_entry))
                                       | None  ->
                                           let tsym =
                                             let uu____2823 =
                                               let uu____2824 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2824 in
                                             varops.mk_unique uu____2823 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2831 =
                                               FStar_Options.log_queries () in
                                             if uu____2831
                                             then
                                               let uu____2833 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2833
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2839 =
                                               let uu____2843 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2843) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2839 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2851 =
                                               let uu____2855 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2855, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2851 in
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
                                             let uu____2868 =
                                               let uu____2872 =
                                                 let uu____2873 =
                                                   let uu____2879 =
                                                     let uu____2880 =
                                                       let uu____2883 =
                                                         let uu____2884 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2884 in
                                                       (f_has_t, uu____2883) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2880 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2879) in
                                                 mkForall_fuel uu____2873 in
                                               (uu____2872,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2868 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2897 =
                                               let uu____2901 =
                                                 let uu____2902 =
                                                   let uu____2908 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2908) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2902 in
                                               (uu____2901, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2897 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2922 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2922);
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
                     let uu____2933 =
                       let uu____2937 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2937, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2933 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2946 =
                       let uu____2950 =
                         let uu____2951 =
                           let uu____2957 =
                             let uu____2958 =
                               let uu____2961 =
                                 let uu____2962 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2962 in
                               (f_has_t, uu____2961) in
                             FStar_SMTEncoding_Util.mkImp uu____2958 in
                           ([[f_has_t]], [fsym], uu____2957) in
                         mkForall_fuel uu____2951 in
                       (uu____2950, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2946 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2976 ->
           let uu____2981 =
             let uu____2984 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2984 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2989;
                 FStar_Syntax_Syntax.pos = uu____2990;
                 FStar_Syntax_Syntax.vars = uu____2991;_} ->
                 let uu____2998 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2998 with
                  | (b,f1) ->
                      let uu____3012 =
                        let uu____3013 = FStar_List.hd b in
                        Prims.fst uu____3013 in
                      (uu____3012, f1))
             | uu____3018 -> failwith "impossible" in
           (match uu____2981 with
            | (x,f) ->
                let uu____3025 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3025 with
                 | (base_t,decls) ->
                     let uu____3032 = gen_term_var env x in
                     (match uu____3032 with
                      | (x1,xtm,env') ->
                          let uu____3041 = encode_formula f env' in
                          (match uu____3041 with
                           | (refinement,decls') ->
                               let uu____3048 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3048 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3059 =
                                        let uu____3061 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3065 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3061
                                          uu____3065 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3059 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3081  ->
                                              match uu____3081 with
                                              | (y,uu____3085) ->
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
                                    let uu____3104 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3104 with
                                     | Some cache_entry ->
                                         let uu____3109 =
                                           let uu____3110 =
                                             let uu____3114 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3114) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3110 in
                                         (uu____3109,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3126 =
                                             let uu____3127 =
                                               let uu____3128 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3128 in
                                             Prims.strcat module_name
                                               uu____3127 in
                                           varops.mk_unique uu____3126 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3137 =
                                             let uu____3141 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3141) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3137 in
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
                                           let uu____3151 =
                                             let uu____3155 =
                                               let uu____3156 =
                                                 let uu____3162 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3162) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3156 in
                                             (uu____3155,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3151 in
                                         let t_kinding =
                                           let uu____3172 =
                                             let uu____3176 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3176,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3172 in
                                         let t_interp =
                                           let uu____3186 =
                                             let uu____3190 =
                                               let uu____3191 =
                                                 let uu____3197 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3197) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3191 in
                                             let uu____3209 =
                                               let uu____3211 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3211 in
                                             (uu____3190, uu____3209,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3186 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3216 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3216);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3233 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3233 in
           let uu____3237 = encode_term_pred None k env ttm in
           (match uu____3237 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3245 =
                    let uu____3249 =
                      let uu____3250 =
                        let uu____3251 =
                          let uu____3252 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3252 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3251 in
                      varops.mk_unique uu____3250 in
                    (t_has_k, (Some "Uvar typing"), uu____3249) in
                  FStar_SMTEncoding_Util.mkAssume uu____3245 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3258 ->
           let uu____3268 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3268 with
            | (head1,args_e) ->
                let uu____3296 =
                  let uu____3304 =
                    let uu____3305 = FStar_Syntax_Subst.compress head1 in
                    uu____3305.FStar_Syntax_Syntax.n in
                  (uu____3304, args_e) in
                (match uu____3296 with
                 | (uu____3315,uu____3316) when head_redex env head1 ->
                     let uu____3327 = whnf env t in
                     encode_term uu____3327 env
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
                     let uu____3401 = encode_term v1 env in
                     (match uu____3401 with
                      | (v11,decls1) ->
                          let uu____3408 = encode_term v2 env in
                          (match uu____3408 with
                           | (v21,decls2) ->
                               let uu____3415 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3415,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3417) ->
                     let e0 =
                       let uu____3429 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3429 in
                     ((let uu____3435 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3435
                       then
                         let uu____3436 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3436
                       else ());
                      (let e =
                         let uu____3441 =
                           let uu____3442 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3443 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3442
                             uu____3443 in
                         uu____3441 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3452),(arg,uu____3454)::[]) -> encode_term arg env
                 | uu____3472 ->
                     let uu____3480 = encode_args args_e env in
                     (match uu____3480 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3513 = encode_term head1 env in
                            match uu____3513 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3552 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3552 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3594  ->
                                                 fun uu____3595  ->
                                                   match (uu____3594,
                                                           uu____3595)
                                                   with
                                                   | ((bv,uu____3609),
                                                      (a,uu____3611)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3625 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3625
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3630 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3630 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3640 =
                                                   let uu____3644 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3649 =
                                                     let uu____3650 =
                                                       let uu____3651 =
                                                         let uu____3652 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3652 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3651 in
                                                     varops.mk_unique
                                                       uu____3650 in
                                                   (uu____3644,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3649) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3640 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3669 = lookup_free_var_sym env fv in
                            match uu____3669 with
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
                                let uu____3707 =
                                  let uu____3708 =
                                    let uu____3711 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3711 Prims.fst in
                                  FStar_All.pipe_right uu____3708 Prims.snd in
                                Some uu____3707
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3730,(FStar_Util.Inl t1,uu____3732),uu____3733)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3771,(FStar_Util.Inr c,uu____3773),uu____3774)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3812 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3832 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3832 in
                               let uu____3833 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3833 with
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
                                     | uu____3858 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3903 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3903 with
            | (bs1,body1,opening) ->
                let fallback uu____3918 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3923 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3923, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3934 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3934
                  | FStar_Util.Inr (eff,uu____3936) ->
                      let uu____3942 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3942 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3987 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___139_3988 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___139_3988.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___139_3988.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___139_3988.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___139_3988.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___139_3988.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___139_3988.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___139_3988.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___139_3988.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___139_3988.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___139_3988.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___139_3988.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___139_3988.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___139_3988.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___139_3988.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___139_3988.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___139_3988.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___139_3988.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___139_3988.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___139_3988.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___139_3988.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___139_3988.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___139_3988.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___139_3988.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____3987 FStar_Syntax_Syntax.U_unknown in
                        let uu____3989 =
                          let uu____3990 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3990 in
                        FStar_Util.Inl uu____3989
                    | FStar_Util.Inr (eff_name,uu____3997) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4028 =
                        let uu____4029 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4029 in
                      FStar_All.pipe_right uu____4028
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4041 =
                        let uu____4042 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4042 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4050 =
                          let uu____4051 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4051 in
                        FStar_All.pipe_right uu____4050
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4055 =
                             let uu____4056 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4056 in
                           FStar_All.pipe_right uu____4055
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4067 =
                         let uu____4068 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4068 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4067);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4083 =
                       (is_impure lc1) &&
                         (let uu____4084 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4084) in
                     if uu____4083
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4089 = encode_binders None bs1 env in
                        match uu____4089 with
                        | (vars,guards,envbody,decls,uu____4104) ->
                            let uu____4111 =
                              let uu____4119 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4119
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4111 with
                             | (lc2,body2) ->
                                 let uu____4144 = encode_term body2 envbody in
                                 (match uu____4144 with
                                  | (body3,decls') ->
                                      let uu____4151 =
                                        let uu____4156 = codomain_eff lc2 in
                                        match uu____4156 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4168 =
                                              encode_term tfun env in
                                            (match uu____4168 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4151 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4187 =
                                               let uu____4193 =
                                                 let uu____4194 =
                                                   let uu____4197 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4197, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4194 in
                                               ([], vars, uu____4193) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4187 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4205 =
                                                   let uu____4207 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4207 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4205 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4218 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4218 with
                                            | Some cache_entry ->
                                                let uu____4223 =
                                                  let uu____4224 =
                                                    let uu____4228 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4228) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4224 in
                                                (uu____4223,
                                                  (use_cache_entry
                                                     cache_entry))
                                            | None  ->
                                                let uu____4234 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4234 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4241 =
                                                         let uu____4242 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4242 =
                                                           cache_size in
                                                       if uu____4241
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
                                                         let uu____4253 =
                                                           let uu____4254 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4254 in
                                                         varops.mk_unique
                                                           uu____4253 in
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
                                                       let uu____4259 =
                                                         let uu____4263 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4263) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4259 in
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
                                                           let uu____4275 =
                                                             let uu____4276 =
                                                               let uu____4280
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4280,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4276 in
                                                           [uu____4275] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4288 =
                                                         let uu____4292 =
                                                           let uu____4293 =
                                                             let uu____4299 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4299) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4293 in
                                                         (uu____4292,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4288 in
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
                                                     ((let uu____4309 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4309);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4311,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4312;
                          FStar_Syntax_Syntax.lbunivs = uu____4313;
                          FStar_Syntax_Syntax.lbtyp = uu____4314;
                          FStar_Syntax_Syntax.lbeff = uu____4315;
                          FStar_Syntax_Syntax.lbdef = uu____4316;_}::uu____4317),uu____4318)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4336;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4338;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4354 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4367 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4367, [decl_e])))
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
              let uu____4409 = encode_term e1 env in
              match uu____4409 with
              | (ee1,decls1) ->
                  let uu____4416 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4416 with
                   | (xs,e21) ->
                       let uu____4430 = FStar_List.hd xs in
                       (match uu____4430 with
                        | (x1,uu____4438) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4440 = encode_body e21 env' in
                            (match uu____4440 with
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
            let uu____4462 =
              let uu____4466 =
                let uu____4467 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4467 in
              gen_term_var env uu____4466 in
            match uu____4462 with
            | (scrsym,scr',env1) ->
                let uu____4481 = encode_term e env1 in
                (match uu____4481 with
                 | (scr,decls) ->
                     let uu____4488 =
                       let encode_branch b uu____4504 =
                         match uu____4504 with
                         | (else_case,decls1) ->
                             let uu____4515 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4515 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4545  ->
                                       fun uu____4546  ->
                                         match (uu____4545, uu____4546) with
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
                                                       fun uu____4583  ->
                                                         match uu____4583
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4588 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4603 =
                                                     encode_term w1 env2 in
                                                   (match uu____4603 with
                                                    | (w2,decls21) ->
                                                        let uu____4611 =
                                                          let uu____4612 =
                                                            let uu____4615 =
                                                              let uu____4616
                                                                =
                                                                let uu____4619
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4619) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4616 in
                                                            (guard,
                                                              uu____4615) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4612 in
                                                        (uu____4611, decls21)) in
                                             (match uu____4588 with
                                              | (guard1,decls21) ->
                                                  let uu____4627 =
                                                    encode_br br env2 in
                                                  (match uu____4627 with
                                                   | (br1,decls3) ->
                                                       let uu____4635 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4635,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4488 with
                      | (match_tm,decls1) ->
                          let uu____4647 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4647, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4678 -> let uu____4679 = encode_one_pat env pat in [uu____4679]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4691 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4691
       then
         let uu____4692 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4692
       else ());
      (let uu____4694 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4694 with
       | (vars,pat_term) ->
           let uu____4704 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4727  ->
                     fun v1  ->
                       match uu____4727 with
                       | (env1,vars1) ->
                           let uu____4755 = gen_term_var env1 v1 in
                           (match uu____4755 with
                            | (xx,uu____4767,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4704 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4814 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4822 =
                        let uu____4825 = encode_const c in
                        (scrutinee, uu____4825) in
                      FStar_SMTEncoding_Util.mkEq uu____4822
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4844 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4844 with
                        | (uu____4848,uu____4849::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4851 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4872  ->
                                  match uu____4872 with
                                  | (arg,uu____4878) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4888 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4888)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4907 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4922 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4937 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4959  ->
                                  match uu____4959 with
                                  | (arg,uu____4968) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4978 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4978)) in
                      FStar_All.pipe_right uu____4937 FStar_List.flatten in
                let pat_term1 uu____4994 = encode_term pat_term env1 in
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
      let uu____5001 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5016  ->
                fun uu____5017  ->
                  match (uu____5016, uu____5017) with
                  | ((tms,decls),(t,uu____5037)) ->
                      let uu____5048 = encode_term t env in
                      (match uu____5048 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5001 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.term Prims.option ->
    FStar_Syntax_Syntax.typ ->
      env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun new_pats  ->
    fun t  ->
      fun env  ->
        let list_elements1 e =
          let uu____5084 = FStar_Syntax_Util.list_elements e in
          match uu____5084 with
          | Some l -> l
          | None  ->
              (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                 "SMT pattern is not a list literal; ignoring the pattern";
               []) in
        let one_pat p =
          let uu____5099 =
            let uu____5109 = FStar_Syntax_Util.unmeta p in
            FStar_All.pipe_right uu____5109 FStar_Syntax_Util.head_and_args in
          match uu____5099 with
          | (head1,args) ->
              let uu____5137 =
                let uu____5145 =
                  let uu____5146 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5146.FStar_Syntax_Syntax.n in
                (uu____5145, args) in
              (match uu____5137 with
               | (FStar_Syntax_Syntax.Tm_fvar
                  fv,(uu____5157,uu____5158)::(e,uu____5160)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpat_lid
                   -> e
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5188)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatT_lid
                   -> e
               | uu____5206 -> failwith "Unexpected pattern term") in
        let lemma_pats p =
          let elts = list_elements1 p in
          let smt_pat_or t1 =
            let uu____5233 =
              let uu____5243 = FStar_Syntax_Util.unmeta t1 in
              FStar_All.pipe_right uu____5243 FStar_Syntax_Util.head_and_args in
            match uu____5233 with
            | (head1,args) ->
                let uu____5272 =
                  let uu____5280 =
                    let uu____5281 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5281.FStar_Syntax_Syntax.n in
                  (uu____5280, args) in
                (match uu____5272 with
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5294)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatOr_lid
                     -> Some e
                 | uu____5314 -> None) in
          match elts with
          | t1::[] ->
              let uu____5329 = smt_pat_or t1 in
              (match uu____5329 with
               | Some e ->
                   let uu____5342 = list_elements1 e in
                   FStar_All.pipe_right uu____5342
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5353 = list_elements1 branch1 in
                           FStar_All.pipe_right uu____5353
                             (FStar_List.map one_pat)))
               | uu____5361 ->
                   let uu____5365 =
                     FStar_All.pipe_right elts (FStar_List.map one_pat) in
                   [uu____5365])
          | uu____5381 ->
              let uu____5383 =
                FStar_All.pipe_right elts (FStar_List.map one_pat) in
              [uu____5383] in
        let uu____5399 =
          let uu____5412 =
            let uu____5413 = FStar_Syntax_Subst.compress t in
            uu____5413.FStar_Syntax_Syntax.n in
          match uu____5412 with
          | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
              let uu____5440 = FStar_Syntax_Subst.open_comp binders c in
              (match uu____5440 with
               | (binders1,c1) ->
                   (match c1.FStar_Syntax_Syntax.n with
                    | FStar_Syntax_Syntax.Comp
                        { FStar_Syntax_Syntax.comp_univs = uu____5469;
                          FStar_Syntax_Syntax.effect_name = uu____5470;
                          FStar_Syntax_Syntax.result_typ = uu____5471;
                          FStar_Syntax_Syntax.effect_args =
                            (pre,uu____5473)::(post,uu____5475)::(pats,uu____5477)::[];
                          FStar_Syntax_Syntax.flags = uu____5478;_}
                        ->
                        let pats' =
                          match new_pats with
                          | Some new_pats' -> new_pats'
                          | None  -> pats in
                        let uu____5512 = lemma_pats pats' in
                        (binders1, pre, post, uu____5512)
                    | uu____5525 -> failwith "impos"))
          | uu____5538 -> failwith "Impos" in
        match uu____5399 with
        | (binders,pre,post,patterns) ->
            let env1 =
              let uu___140_5574 = env in
              let uu____5575 =
                let uu____5577 =
                  FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "0") in
                Some uu____5577 in
              {
                bindings = (uu___140_5574.bindings);
                depth = (uu___140_5574.depth);
                tcenv = (uu___140_5574.tcenv);
                warn = (uu___140_5574.warn);
                cache = (uu___140_5574.cache);
                nolabels = (uu___140_5574.nolabels);
                use_fuel_instrumented_version = uu____5575;
                encode_non_total_function_typ =
                  (uu___140_5574.encode_non_total_function_typ);
                current_module_name = (uu___140_5574.current_module_name)
              } in
            let uu____5578 = encode_binders None binders env1 in
            (match uu____5578 with
             | (vars,guards,env2,decls,uu____5593) ->
                 let uu____5600 =
                   let env3 =
                     let uu___141_5608 = env2 in
                     let uu____5609 =
                       let uu____5611 =
                         FStar_SMTEncoding_Term.n_fuel (Prims.parse_int "1") in
                       Some uu____5611 in
                     {
                       bindings = (uu___141_5608.bindings);
                       depth = (uu___141_5608.depth);
                       tcenv = (uu___141_5608.tcenv);
                       warn = (uu___141_5608.warn);
                       cache = (uu___141_5608.cache);
                       nolabels = (uu___141_5608.nolabels);
                       use_fuel_instrumented_version = uu____5609;
                       encode_non_total_function_typ =
                         (uu___141_5608.encode_non_total_function_typ);
                       current_module_name =
                         (uu___141_5608.current_module_name)
                     } in
                   let uu____5612 =
                     FStar_All.pipe_right patterns
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5634 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun t1  -> encode_term t1 env3)) in
                             FStar_All.pipe_right uu____5634 FStar_List.unzip)) in
                   FStar_All.pipe_right uu____5612 FStar_List.unzip in
                 (match uu____5600 with
                  | (pats,decls') ->
                      let decls'1 = FStar_List.flatten decls' in
                      let env3 =
                        let uu___142_5680 = env2 in
                        {
                          bindings = (uu___142_5680.bindings);
                          depth = (uu___142_5680.depth);
                          tcenv = (uu___142_5680.tcenv);
                          warn = (uu___142_5680.warn);
                          cache = (uu___142_5680.cache);
                          nolabels = true;
                          use_fuel_instrumented_version =
                            (uu___142_5680.use_fuel_instrumented_version);
                          encode_non_total_function_typ =
                            (uu___142_5680.encode_non_total_function_typ);
                          current_module_name =
                            (uu___142_5680.current_module_name)
                        } in
                      let uu____5681 =
                        let uu____5684 = FStar_Syntax_Util.unmeta pre in
                        encode_formula uu____5684 env3 in
                      (match uu____5681 with
                       | (pre1,decls'') ->
                           let uu____5689 =
                             let uu____5692 = FStar_Syntax_Util.unmeta post in
                             encode_formula uu____5692 env3 in
                           (match uu____5689 with
                            | (post1,decls''') ->
                                let decls1 =
                                  FStar_List.append decls
                                    (FStar_List.append
                                       (FStar_List.flatten decls'1)
                                       (FStar_List.append decls'' decls''')) in
                                let uu____5699 =
                                  let uu____5700 =
                                    let uu____5706 =
                                      let uu____5707 =
                                        let uu____5710 =
                                          FStar_SMTEncoding_Util.mk_and_l
                                            (pre1 :: guards) in
                                        (uu____5710, post1) in
                                      FStar_SMTEncoding_Util.mkImp uu____5707 in
                                    (pats, vars, uu____5706) in
                                  FStar_SMTEncoding_Util.mkForall uu____5700 in
                                (uu____5699, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5723 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5723
        then
          let uu____5724 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5725 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5724 uu____5725
        else () in
      let enc f r l =
        let uu____5752 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5765 = encode_term (Prims.fst x) env in
                 match uu____5765 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5752 with
        | (decls,args) ->
            let uu____5782 =
              let uu___143_5783 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___143_5783.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___143_5783.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5782, decls) in
      let const_op f r uu____5802 = let uu____5805 = f r in (uu____5805, []) in
      let un_op f l =
        let uu____5821 = FStar_List.hd l in FStar_All.pipe_left f uu____5821 in
      let bin_op f uu___114_5834 =
        match uu___114_5834 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5842 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5869 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5878  ->
                 match uu____5878 with
                 | (t,uu____5886) ->
                     let uu____5887 = encode_formula t env in
                     (match uu____5887 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____5869 with
        | (decls,phis) ->
            let uu____5904 =
              let uu___144_5905 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_5905.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_5905.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5904, decls) in
      let eq_op r uu___115_5921 =
        match uu___115_5921 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____5981 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____5981 r [e1; e2]
        | l ->
            let uu____6001 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6001 r l in
      let mk_imp1 r uu___116_6020 =
        match uu___116_6020 with
        | (lhs,uu____6024)::(rhs,uu____6026)::[] ->
            let uu____6047 = encode_formula rhs env in
            (match uu____6047 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6056) ->
                      (l1, decls1)
                  | uu____6059 ->
                      let uu____6060 = encode_formula lhs env in
                      (match uu____6060 with
                       | (l2,decls2) ->
                           let uu____6067 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6067, (FStar_List.append decls1 decls2)))))
        | uu____6069 -> failwith "impossible" in
      let mk_ite r uu___117_6084 =
        match uu___117_6084 with
        | (guard,uu____6088)::(_then,uu____6090)::(_else,uu____6092)::[] ->
            let uu____6121 = encode_formula guard env in
            (match uu____6121 with
             | (g,decls1) ->
                 let uu____6128 = encode_formula _then env in
                 (match uu____6128 with
                  | (t,decls2) ->
                      let uu____6135 = encode_formula _else env in
                      (match uu____6135 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6144 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6163 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6163 in
      let connectives =
        let uu____6175 =
          let uu____6184 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6184) in
        let uu____6197 =
          let uu____6207 =
            let uu____6216 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6216) in
          let uu____6229 =
            let uu____6239 =
              let uu____6249 =
                let uu____6258 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6258) in
              let uu____6271 =
                let uu____6281 =
                  let uu____6291 =
                    let uu____6300 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6300) in
                  [uu____6291;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6281 in
              uu____6249 :: uu____6271 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6239 in
          uu____6207 :: uu____6229 in
        uu____6175 :: uu____6197 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6462 = encode_formula phi' env in
            (match uu____6462 with
             | (phi2,decls) ->
                 let uu____6469 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6469, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6470 ->
            let uu____6475 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6475 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6504 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6504 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6512;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6514;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6530 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6530 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6562::(x,uu____6564)::(t,uu____6566)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6600 = encode_term x env in
                 (match uu____6600 with
                  | (x1,decls) ->
                      let uu____6607 = encode_term t env in
                      (match uu____6607 with
                       | (t1,decls') ->
                           let uu____6614 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6614, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6618)::(msg,uu____6620)::(phi2,uu____6622)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6656 =
                   let uu____6659 =
                     let uu____6660 = FStar_Syntax_Subst.compress r in
                     uu____6660.FStar_Syntax_Syntax.n in
                   let uu____6663 =
                     let uu____6664 = FStar_Syntax_Subst.compress msg in
                     uu____6664.FStar_Syntax_Syntax.n in
                   (uu____6659, uu____6663) in
                 (match uu____6656 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6671))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6687 -> fallback phi2)
             | uu____6690 when head_redex env head2 ->
                 let uu____6698 = whnf env phi1 in
                 encode_formula uu____6698 env
             | uu____6699 ->
                 let uu____6707 = encode_term phi1 env in
                 (match uu____6707 with
                  | (tt,decls) ->
                      let uu____6714 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___145_6715 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___145_6715.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___145_6715.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6714, decls)))
        | uu____6718 ->
            let uu____6719 = encode_term phi1 env in
            (match uu____6719 with
             | (tt,decls) ->
                 let uu____6726 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___146_6727 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___146_6727.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___146_6727.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6726, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6754 = encode_binders None bs env1 in
        match uu____6754 with
        | (vars,guards,env2,decls,uu____6776) ->
            let uu____6783 =
              let uu____6790 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6813 =
                          let uu____6818 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6832  ->
                                    match uu____6832 with
                                    | (t,uu____6838) ->
                                        let uu____6839 =
                                          let uu___147_6840 = env2 in
                                          let uu____6841 =
                                            let uu____6843 =
                                              FStar_SMTEncoding_Term.n_fuel
                                                (Prims.parse_int "0") in
                                            Some uu____6843 in
                                          {
                                            bindings =
                                              (uu___147_6840.bindings);
                                            depth = (uu___147_6840.depth);
                                            tcenv = (uu___147_6840.tcenv);
                                            warn = (uu___147_6840.warn);
                                            cache = (uu___147_6840.cache);
                                            nolabels =
                                              (uu___147_6840.nolabels);
                                            use_fuel_instrumented_version =
                                              uu____6841;
                                            encode_non_total_function_typ =
                                              (uu___147_6840.encode_non_total_function_typ);
                                            current_module_name =
                                              (uu___147_6840.current_module_name)
                                          } in
                                        encode_term t uu____6839)) in
                          FStar_All.pipe_right uu____6818 FStar_List.unzip in
                        match uu____6813 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6790 FStar_List.unzip in
            (match uu____6783 with
             | (pats,decls') ->
                 let uu____6895 = encode_formula body env2 in
                 (match uu____6895 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6914;
                             FStar_SMTEncoding_Term.rng = uu____6915;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6923 -> guards in
                      let uu____6926 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____6926, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____6960  ->
                   match uu____6960 with
                   | (x,uu____6964) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____6970 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____6976 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____6976) uu____6970 tl1 in
             let uu____6978 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6990  ->
                       match uu____6990 with
                       | (b,uu____6994) ->
                           let uu____6995 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____6995)) in
             (match uu____6978 with
              | None  -> ()
              | Some (x,uu____6999) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7009 =
                    let uu____7010 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7010 in
                  FStar_Errors.warn pos uu____7009) in
       let uu____7011 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7011 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7017 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7053  ->
                     match uu____7053 with
                     | (l,uu____7063) -> FStar_Ident.lid_equals op l)) in
           (match uu____7017 with
            | None  -> fallback phi1
            | Some (uu____7086,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7115 = encode_q_body env vars pats body in
             match uu____7115 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7141 =
                     let uu____7147 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7147) in
                   FStar_SMTEncoding_Term.mkForall uu____7141
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7159 = encode_q_body env vars pats body in
             match uu____7159 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7184 =
                   let uu____7185 =
                     let uu____7191 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7191) in
                   FStar_SMTEncoding_Term.mkExists uu____7185
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7184, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7240 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7240 with
  | (asym,a) ->
      let uu____7245 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7245 with
       | (xsym,x) ->
           let uu____7250 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7250 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7280 =
                      let uu____7286 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7286, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7280 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7301 =
                      let uu____7305 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7305) in
                    FStar_SMTEncoding_Util.mkApp uu____7301 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7313 =
                    let uu____7315 =
                      let uu____7317 =
                        let uu____7319 =
                          let uu____7320 =
                            let uu____7324 =
                              let uu____7325 =
                                let uu____7331 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7331) in
                              FStar_SMTEncoding_Util.mkForall uu____7325 in
                            (uu____7324, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7320 in
                        let uu____7340 =
                          let uu____7342 =
                            let uu____7343 =
                              let uu____7347 =
                                let uu____7348 =
                                  let uu____7354 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7354) in
                                FStar_SMTEncoding_Util.mkForall uu____7348 in
                              (uu____7347,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7343 in
                          [uu____7342] in
                        uu____7319 :: uu____7340 in
                      xtok_decl :: uu____7317 in
                    xname_decl :: uu____7315 in
                  (xtok1, uu____7313) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7403 =
                    let uu____7411 =
                      let uu____7417 =
                        let uu____7418 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7418 in
                      quant axy uu____7417 in
                    (FStar_Syntax_Const.op_Eq, uu____7411) in
                  let uu____7424 =
                    let uu____7433 =
                      let uu____7441 =
                        let uu____7447 =
                          let uu____7448 =
                            let uu____7449 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7449 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7448 in
                        quant axy uu____7447 in
                      (FStar_Syntax_Const.op_notEq, uu____7441) in
                    let uu____7455 =
                      let uu____7464 =
                        let uu____7472 =
                          let uu____7478 =
                            let uu____7479 =
                              let uu____7480 =
                                let uu____7483 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7484 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7483, uu____7484) in
                              FStar_SMTEncoding_Util.mkLT uu____7480 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7479 in
                          quant xy uu____7478 in
                        (FStar_Syntax_Const.op_LT, uu____7472) in
                      let uu____7490 =
                        let uu____7499 =
                          let uu____7507 =
                            let uu____7513 =
                              let uu____7514 =
                                let uu____7515 =
                                  let uu____7518 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7519 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7518, uu____7519) in
                                FStar_SMTEncoding_Util.mkLTE uu____7515 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7514 in
                            quant xy uu____7513 in
                          (FStar_Syntax_Const.op_LTE, uu____7507) in
                        let uu____7525 =
                          let uu____7534 =
                            let uu____7542 =
                              let uu____7548 =
                                let uu____7549 =
                                  let uu____7550 =
                                    let uu____7553 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7554 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7553, uu____7554) in
                                  FStar_SMTEncoding_Util.mkGT uu____7550 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7549 in
                              quant xy uu____7548 in
                            (FStar_Syntax_Const.op_GT, uu____7542) in
                          let uu____7560 =
                            let uu____7569 =
                              let uu____7577 =
                                let uu____7583 =
                                  let uu____7584 =
                                    let uu____7585 =
                                      let uu____7588 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7589 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7588, uu____7589) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7585 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7584 in
                                quant xy uu____7583 in
                              (FStar_Syntax_Const.op_GTE, uu____7577) in
                            let uu____7595 =
                              let uu____7604 =
                                let uu____7612 =
                                  let uu____7618 =
                                    let uu____7619 =
                                      let uu____7620 =
                                        let uu____7623 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7624 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7623, uu____7624) in
                                      FStar_SMTEncoding_Util.mkSub uu____7620 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7619 in
                                  quant xy uu____7618 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7612) in
                              let uu____7630 =
                                let uu____7639 =
                                  let uu____7647 =
                                    let uu____7653 =
                                      let uu____7654 =
                                        let uu____7655 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7655 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7654 in
                                    quant qx uu____7653 in
                                  (FStar_Syntax_Const.op_Minus, uu____7647) in
                                let uu____7661 =
                                  let uu____7670 =
                                    let uu____7678 =
                                      let uu____7684 =
                                        let uu____7685 =
                                          let uu____7686 =
                                            let uu____7689 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7690 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7689, uu____7690) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7686 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7685 in
                                      quant xy uu____7684 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7678) in
                                  let uu____7696 =
                                    let uu____7705 =
                                      let uu____7713 =
                                        let uu____7719 =
                                          let uu____7720 =
                                            let uu____7721 =
                                              let uu____7724 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7725 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7724, uu____7725) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7721 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7720 in
                                        quant xy uu____7719 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7713) in
                                    let uu____7731 =
                                      let uu____7740 =
                                        let uu____7748 =
                                          let uu____7754 =
                                            let uu____7755 =
                                              let uu____7756 =
                                                let uu____7759 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7760 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7759, uu____7760) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7756 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7755 in
                                          quant xy uu____7754 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7748) in
                                      let uu____7766 =
                                        let uu____7775 =
                                          let uu____7783 =
                                            let uu____7789 =
                                              let uu____7790 =
                                                let uu____7791 =
                                                  let uu____7794 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7795 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7794, uu____7795) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7791 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7790 in
                                            quant xy uu____7789 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7783) in
                                        let uu____7801 =
                                          let uu____7810 =
                                            let uu____7818 =
                                              let uu____7824 =
                                                let uu____7825 =
                                                  let uu____7826 =
                                                    let uu____7829 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7830 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7829, uu____7830) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7826 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7825 in
                                              quant xy uu____7824 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7818) in
                                          let uu____7836 =
                                            let uu____7845 =
                                              let uu____7853 =
                                                let uu____7859 =
                                                  let uu____7860 =
                                                    let uu____7861 =
                                                      let uu____7864 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7865 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7864,
                                                        uu____7865) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7861 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7860 in
                                                quant xy uu____7859 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7853) in
                                            let uu____7871 =
                                              let uu____7880 =
                                                let uu____7888 =
                                                  let uu____7894 =
                                                    let uu____7895 =
                                                      let uu____7896 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7896 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7895 in
                                                  quant qx uu____7894 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7888) in
                                              [uu____7880] in
                                            uu____7845 :: uu____7871 in
                                          uu____7810 :: uu____7836 in
                                        uu____7775 :: uu____7801 in
                                      uu____7740 :: uu____7766 in
                                    uu____7705 :: uu____7731 in
                                  uu____7670 :: uu____7696 in
                                uu____7639 :: uu____7661 in
                              uu____7604 :: uu____7630 in
                            uu____7569 :: uu____7595 in
                          uu____7534 :: uu____7560 in
                        uu____7499 :: uu____7525 in
                      uu____7464 :: uu____7490 in
                    uu____7433 :: uu____7455 in
                  uu____7403 :: uu____7424 in
                let mk1 l v1 =
                  let uu____8024 =
                    let uu____8029 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8061  ->
                              match uu____8061 with
                              | (l',uu____8070) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8029
                      (FStar_Option.map
                         (fun uu____8103  ->
                            match uu____8103 with | (uu____8114,b) -> b v1)) in
                  FStar_All.pipe_right uu____8024 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8155  ->
                          match uu____8155 with
                          | (l',uu____8164) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8190 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8190 with
        | (xxsym,xx) ->
            let uu____8195 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8195 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8203 =
                   let uu____8207 =
                     let uu____8208 =
                       let uu____8214 =
                         let uu____8215 =
                           let uu____8218 =
                             let uu____8219 =
                               let uu____8222 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8222) in
                             FStar_SMTEncoding_Util.mkEq uu____8219 in
                           (xx_has_type, uu____8218) in
                         FStar_SMTEncoding_Util.mkImp uu____8215 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8214) in
                     FStar_SMTEncoding_Util.mkForall uu____8208 in
                   let uu____8235 =
                     let uu____8236 =
                       let uu____8237 =
                         let uu____8238 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8238 in
                       Prims.strcat module_name uu____8237 in
                     varops.mk_unique uu____8236 in
                   (uu____8207, (Some "pretyping"), uu____8235) in
                 FStar_SMTEncoding_Util.mkAssume uu____8203)
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
    let uu____8268 =
      let uu____8269 =
        let uu____8273 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8273, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8269 in
    let uu____8275 =
      let uu____8277 =
        let uu____8278 =
          let uu____8282 =
            let uu____8283 =
              let uu____8289 =
                let uu____8290 =
                  let uu____8293 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8293) in
                FStar_SMTEncoding_Util.mkImp uu____8290 in
              ([[typing_pred]], [xx], uu____8289) in
            mkForall_fuel uu____8283 in
          (uu____8282, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8278 in
      [uu____8277] in
    uu____8268 :: uu____8275 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8321 =
      let uu____8322 =
        let uu____8326 =
          let uu____8327 =
            let uu____8333 =
              let uu____8336 =
                let uu____8338 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8338] in
              [uu____8336] in
            let uu____8341 =
              let uu____8342 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8342 tt in
            (uu____8333, [bb], uu____8341) in
          FStar_SMTEncoding_Util.mkForall uu____8327 in
        (uu____8326, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8322 in
    let uu____8353 =
      let uu____8355 =
        let uu____8356 =
          let uu____8360 =
            let uu____8361 =
              let uu____8367 =
                let uu____8368 =
                  let uu____8371 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8371) in
                FStar_SMTEncoding_Util.mkImp uu____8368 in
              ([[typing_pred]], [xx], uu____8367) in
            mkForall_fuel uu____8361 in
          (uu____8360, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8356 in
      [uu____8355] in
    uu____8321 :: uu____8353 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8405 =
        let uu____8406 =
          let uu____8410 =
            let uu____8412 =
              let uu____8414 =
                let uu____8416 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8417 =
                  let uu____8419 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8419] in
                uu____8416 :: uu____8417 in
              tt :: uu____8414 in
            tt :: uu____8412 in
          ("Prims.Precedes", uu____8410) in
        FStar_SMTEncoding_Util.mkApp uu____8406 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8405 in
    let precedes_y_x =
      let uu____8422 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8422 in
    let uu____8424 =
      let uu____8425 =
        let uu____8429 =
          let uu____8430 =
            let uu____8436 =
              let uu____8439 =
                let uu____8441 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8441] in
              [uu____8439] in
            let uu____8444 =
              let uu____8445 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8445 tt in
            (uu____8436, [bb], uu____8444) in
          FStar_SMTEncoding_Util.mkForall uu____8430 in
        (uu____8429, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8425 in
    let uu____8456 =
      let uu____8458 =
        let uu____8459 =
          let uu____8463 =
            let uu____8464 =
              let uu____8470 =
                let uu____8471 =
                  let uu____8474 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8474) in
                FStar_SMTEncoding_Util.mkImp uu____8471 in
              ([[typing_pred]], [xx], uu____8470) in
            mkForall_fuel uu____8464 in
          (uu____8463, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8459 in
      let uu____8487 =
        let uu____8489 =
          let uu____8490 =
            let uu____8494 =
              let uu____8495 =
                let uu____8501 =
                  let uu____8502 =
                    let uu____8505 =
                      let uu____8506 =
                        let uu____8508 =
                          let uu____8510 =
                            let uu____8512 =
                              let uu____8513 =
                                let uu____8516 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8517 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8516, uu____8517) in
                              FStar_SMTEncoding_Util.mkGT uu____8513 in
                            let uu____8518 =
                              let uu____8520 =
                                let uu____8521 =
                                  let uu____8524 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8525 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8524, uu____8525) in
                                FStar_SMTEncoding_Util.mkGTE uu____8521 in
                              let uu____8526 =
                                let uu____8528 =
                                  let uu____8529 =
                                    let uu____8532 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8533 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8532, uu____8533) in
                                  FStar_SMTEncoding_Util.mkLT uu____8529 in
                                [uu____8528] in
                              uu____8520 :: uu____8526 in
                            uu____8512 :: uu____8518 in
                          typing_pred_y :: uu____8510 in
                        typing_pred :: uu____8508 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8506 in
                    (uu____8505, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8502 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8501) in
              mkForall_fuel uu____8495 in
            (uu____8494, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8490 in
        [uu____8489] in
      uu____8458 :: uu____8487 in
    uu____8424 :: uu____8456 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8563 =
      let uu____8564 =
        let uu____8568 =
          let uu____8569 =
            let uu____8575 =
              let uu____8578 =
                let uu____8580 = FStar_SMTEncoding_Term.boxString b in
                [uu____8580] in
              [uu____8578] in
            let uu____8583 =
              let uu____8584 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8584 tt in
            (uu____8575, [bb], uu____8583) in
          FStar_SMTEncoding_Util.mkForall uu____8569 in
        (uu____8568, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8564 in
    let uu____8595 =
      let uu____8597 =
        let uu____8598 =
          let uu____8602 =
            let uu____8603 =
              let uu____8609 =
                let uu____8610 =
                  let uu____8613 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8613) in
                FStar_SMTEncoding_Util.mkImp uu____8610 in
              ([[typing_pred]], [xx], uu____8609) in
            mkForall_fuel uu____8603 in
          (uu____8602, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8598 in
      [uu____8597] in
    uu____8563 :: uu____8595 in
  let mk_ref1 env reft_name uu____8635 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8646 =
        let uu____8650 =
          let uu____8652 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8652] in
        (reft_name, uu____8650) in
      FStar_SMTEncoding_Util.mkApp uu____8646 in
    let refb =
      let uu____8655 =
        let uu____8659 =
          let uu____8661 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8661] in
        (reft_name, uu____8659) in
      FStar_SMTEncoding_Util.mkApp uu____8655 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8665 =
      let uu____8666 =
        let uu____8670 =
          let uu____8671 =
            let uu____8677 =
              let uu____8678 =
                let uu____8681 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8681) in
              FStar_SMTEncoding_Util.mkImp uu____8678 in
            ([[typing_pred]], [xx; aa], uu____8677) in
          mkForall_fuel uu____8671 in
        (uu____8670, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8666 in
    [uu____8665] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8721 =
      let uu____8722 =
        let uu____8726 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8726, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8722 in
    [uu____8721] in
  let mk_and_interp env conj uu____8737 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8754 =
      let uu____8755 =
        let uu____8759 =
          let uu____8760 =
            let uu____8766 =
              let uu____8767 =
                let uu____8770 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8770, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8767 in
            ([[l_and_a_b]], [aa; bb], uu____8766) in
          FStar_SMTEncoding_Util.mkForall uu____8760 in
        (uu____8759, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8755 in
    [uu____8754] in
  let mk_or_interp env disj uu____8794 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8811 =
      let uu____8812 =
        let uu____8816 =
          let uu____8817 =
            let uu____8823 =
              let uu____8824 =
                let uu____8827 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8827, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8824 in
            ([[l_or_a_b]], [aa; bb], uu____8823) in
          FStar_SMTEncoding_Util.mkForall uu____8817 in
        (uu____8816, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8812 in
    [uu____8811] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____8868 =
      let uu____8869 =
        let uu____8873 =
          let uu____8874 =
            let uu____8880 =
              let uu____8881 =
                let uu____8884 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8884, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8881 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____8880) in
          FStar_SMTEncoding_Util.mkForall uu____8874 in
        (uu____8873, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8869 in
    [uu____8868] in
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
    let uu____8931 =
      let uu____8932 =
        let uu____8936 =
          let uu____8937 =
            let uu____8943 =
              let uu____8944 =
                let uu____8947 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8947, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8944 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____8943) in
          FStar_SMTEncoding_Util.mkForall uu____8937 in
        (uu____8936, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8932 in
    [uu____8931] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8992 =
      let uu____8993 =
        let uu____8997 =
          let uu____8998 =
            let uu____9004 =
              let uu____9005 =
                let uu____9008 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9008, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9005 in
            ([[l_imp_a_b]], [aa; bb], uu____9004) in
          FStar_SMTEncoding_Util.mkForall uu____8998 in
        (uu____8997, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8993 in
    [uu____8992] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9049 =
      let uu____9050 =
        let uu____9054 =
          let uu____9055 =
            let uu____9061 =
              let uu____9062 =
                let uu____9065 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9065, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9062 in
            ([[l_iff_a_b]], [aa; bb], uu____9061) in
          FStar_SMTEncoding_Util.mkForall uu____9055 in
        (uu____9054, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9050 in
    [uu____9049] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9099 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9099 in
    let uu____9101 =
      let uu____9102 =
        let uu____9106 =
          let uu____9107 =
            let uu____9113 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9113) in
          FStar_SMTEncoding_Util.mkForall uu____9107 in
        (uu____9106, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9102 in
    [uu____9101] in
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
      let uu____9153 =
        let uu____9157 =
          let uu____9159 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9159] in
        ("Valid", uu____9157) in
      FStar_SMTEncoding_Util.mkApp uu____9153 in
    let uu____9161 =
      let uu____9162 =
        let uu____9166 =
          let uu____9167 =
            let uu____9173 =
              let uu____9174 =
                let uu____9177 =
                  let uu____9178 =
                    let uu____9184 =
                      let uu____9187 =
                        let uu____9189 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9189] in
                      [uu____9187] in
                    let uu____9192 =
                      let uu____9193 =
                        let uu____9196 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9196, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9193 in
                    (uu____9184, [xx1], uu____9192) in
                  FStar_SMTEncoding_Util.mkForall uu____9178 in
                (uu____9177, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9174 in
            ([[l_forall_a_b]], [aa; bb], uu____9173) in
          FStar_SMTEncoding_Util.mkForall uu____9167 in
        (uu____9166, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9162 in
    [uu____9161] in
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
      let uu____9247 =
        let uu____9251 =
          let uu____9253 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9253] in
        ("Valid", uu____9251) in
      FStar_SMTEncoding_Util.mkApp uu____9247 in
    let uu____9255 =
      let uu____9256 =
        let uu____9260 =
          let uu____9261 =
            let uu____9267 =
              let uu____9268 =
                let uu____9271 =
                  let uu____9272 =
                    let uu____9278 =
                      let uu____9281 =
                        let uu____9283 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9283] in
                      [uu____9281] in
                    let uu____9286 =
                      let uu____9287 =
                        let uu____9290 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9290, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9287 in
                    (uu____9278, [xx1], uu____9286) in
                  FStar_SMTEncoding_Util.mkExists uu____9272 in
                (uu____9271, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9268 in
            ([[l_exists_a_b]], [aa; bb], uu____9267) in
          FStar_SMTEncoding_Util.mkForall uu____9261 in
        (uu____9260, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9256 in
    [uu____9255] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9326 =
      let uu____9327 =
        let uu____9331 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9332 = varops.mk_unique "typing_range_const" in
        (uu____9331, (Some "Range_const typing"), uu____9332) in
      FStar_SMTEncoding_Util.mkAssume uu____9327 in
    [uu____9326] in
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
          let uu____9594 =
            FStar_Util.find_opt
              (fun uu____9612  ->
                 match uu____9612 with
                 | (l,uu____9622) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9594 with
          | None  -> []
          | Some (uu____9644,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9681 = encode_function_type_as_formula None t env in
        match uu____9681 with
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
            let uu____9713 =
              (let uu____9714 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9714) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9713
            then
              let uu____9718 = new_term_constant_and_tok_from_lid env lid in
              match uu____9718 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9730 =
                      let uu____9731 = FStar_Syntax_Subst.compress t_norm in
                      uu____9731.FStar_Syntax_Syntax.n in
                    match uu____9730 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9736) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9753  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9756 -> [] in
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
              (let uu____9765 = prims.is lid in
               if uu____9765
               then
                 let vname = varops.new_fvar lid in
                 let uu____9770 = prims.mk lid vname in
                 match uu____9770 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9785 =
                    let uu____9791 = curried_arrow_formals_comp t_norm in
                    match uu____9791 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9802 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9802
                          then
                            let uu____9803 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___148_9804 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___148_9804.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___148_9804.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___148_9804.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___148_9804.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___148_9804.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___148_9804.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___148_9804.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___148_9804.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___148_9804.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___148_9804.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___148_9804.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___148_9804.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___148_9804.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___148_9804.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___148_9804.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___148_9804.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___148_9804.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___148_9804.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___148_9804.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___148_9804.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___148_9804.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___148_9804.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___148_9804.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9803
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9811 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9811)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9785 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9838 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____9838 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9851 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___118_9875  ->
                                     match uu___118_9875 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9878 =
                                           FStar_Util.prefix vars in
                                         (match uu____9878 with
                                          | (uu____9889,(xxsym,uu____9891))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____9901 =
                                                let uu____9902 =
                                                  let uu____9906 =
                                                    let uu____9907 =
                                                      let uu____9913 =
                                                        let uu____9914 =
                                                          let uu____9917 =
                                                            let uu____9918 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____9918 in
                                                          (vapp, uu____9917) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9914 in
                                                      ([[vapp]], vars,
                                                        uu____9913) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9907 in
                                                  (uu____9906,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9902 in
                                              [uu____9901])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____9929 =
                                           FStar_Util.prefix vars in
                                         (match uu____9929 with
                                          | (uu____9940,(xxsym,uu____9942))
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
                                              let uu____9956 =
                                                let uu____9957 =
                                                  let uu____9961 =
                                                    let uu____9962 =
                                                      let uu____9968 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____9968) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9962 in
                                                  (uu____9961,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9957 in
                                              [uu____9956])
                                     | uu____9977 -> [])) in
                           let uu____9978 = encode_binders None formals env1 in
                           (match uu____9978 with
                            | (vars,guards,env',decls1,uu____9994) ->
                                let uu____10001 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10006 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10006, decls1)
                                  | Some p ->
                                      let uu____10008 = encode_formula p env' in
                                      (match uu____10008 with
                                       | (g,ds) ->
                                           let uu____10015 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10015,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10001 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10024 =
                                         let uu____10028 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10028) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10024 in
                                     let uu____10033 =
                                       let vname_decl =
                                         let uu____10038 =
                                           let uu____10044 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10049  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10044,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10038 in
                                       let uu____10054 =
                                         let env2 =
                                           let uu___149_10058 = env1 in
                                           {
                                             bindings =
                                               (uu___149_10058.bindings);
                                             depth = (uu___149_10058.depth);
                                             tcenv = (uu___149_10058.tcenv);
                                             warn = (uu___149_10058.warn);
                                             cache = (uu___149_10058.cache);
                                             nolabels =
                                               (uu___149_10058.nolabels);
                                             use_fuel_instrumented_version =
                                               (uu___149_10058.use_fuel_instrumented_version);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___149_10058.current_module_name)
                                           } in
                                         let uu____10059 =
                                           let uu____10060 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10060 in
                                         if uu____10059
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10054 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10070::uu____10071 ->
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
                                                   let uu____10094 =
                                                     let uu____10100 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10100) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10094 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10114 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10116 =
                                             match formals with
                                             | [] ->
                                                 let uu____10125 =
                                                   let uu____10126 =
                                                     let uu____10128 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10128 in
                                                   push_free_var env1 lid
                                                     vname uu____10126 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10125)
                                             | uu____10131 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10136 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10136 in
                                                 let name_tok_corr =
                                                   let uu____10138 =
                                                     let uu____10142 =
                                                       let uu____10143 =
                                                         let uu____10149 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10149) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10143 in
                                                     (uu____10142,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10138 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10116 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10033 with
                                      | (decls2,env2) ->
                                          let uu____10173 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10178 =
                                              encode_term res_t1 env' in
                                            match uu____10178 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10186 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10186,
                                                  decls) in
                                          (match uu____10173 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10194 =
                                                   let uu____10198 =
                                                     let uu____10199 =
                                                       let uu____10205 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10205) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10199 in
                                                   (uu____10198,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10194 in
                                               let freshness =
                                                 let uu____10214 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10214
                                                 then
                                                   let uu____10217 =
                                                     let uu____10218 =
                                                       let uu____10224 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10230 =
                                                         varops.next_id () in
                                                       (vname, uu____10224,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10230) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10218 in
                                                   let uu____10232 =
                                                     let uu____10234 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10234] in
                                                   uu____10217 :: uu____10232
                                                 else [] in
                                               let g =
                                                 let uu____10238 =
                                                   let uu____10240 =
                                                     let uu____10242 =
                                                       let uu____10244 =
                                                         let uu____10246 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10246 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10244 in
                                                     FStar_List.append decls3
                                                       uu____10242 in
                                                   FStar_List.append decls2
                                                     uu____10240 in
                                                 FStar_List.append decls11
                                                   uu____10238 in
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
          let uu____10268 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10268 with
          | None  ->
              let uu____10295 = encode_free_var env x t t_norm [] in
              (match uu____10295 with
               | (decls,env1) ->
                   let uu____10310 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10310 with
                    | (n1,x',uu____10331) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10347) -> ((n1, x1), [], env)
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
          let uu____10386 = encode_free_var env lid t tt quals in
          match uu____10386 with
          | (decls,env1) ->
              let uu____10397 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10397
              then
                let uu____10401 =
                  let uu____10403 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10403 in
                (uu____10401, env1)
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
             (fun uu____10431  ->
                fun lb  ->
                  match uu____10431 with
                  | (decls,env1) ->
                      let uu____10443 =
                        let uu____10447 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10447
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10443 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10461 = FStar_Syntax_Util.head_and_args t in
    match uu____10461 with
    | (hd1,args) ->
        let uu____10487 =
          let uu____10488 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10488.FStar_Syntax_Syntax.n in
        (match uu____10487 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10492,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10505 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10520  ->
      fun quals  ->
        match uu____10520 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10569 = FStar_Util.first_N nbinders formals in
              match uu____10569 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10609  ->
                         fun uu____10610  ->
                           match (uu____10609, uu____10610) with
                           | ((formal,uu____10620),(binder,uu____10622)) ->
                               let uu____10627 =
                                 let uu____10632 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10632) in
                               FStar_Syntax_Syntax.NT uu____10627) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10637 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10651  ->
                              match uu____10651 with
                              | (x,i) ->
                                  let uu____10658 =
                                    let uu___150_10659 = x in
                                    let uu____10660 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___150_10659.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___150_10659.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10660
                                    } in
                                  (uu____10658, i))) in
                    FStar_All.pipe_right uu____10637
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10672 =
                      let uu____10674 =
                        let uu____10675 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10675.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10674 in
                    let uu____10679 =
                      let uu____10680 = FStar_Syntax_Subst.compress body in
                      let uu____10681 =
                        let uu____10682 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10682 in
                      FStar_Syntax_Syntax.extend_app_n uu____10680
                        uu____10681 in
                    uu____10679 uu____10672 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10724 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10724
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___151_10725 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___151_10725.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___151_10725.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___151_10725.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___151_10725.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___151_10725.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___151_10725.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___151_10725.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___151_10725.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___151_10725.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___151_10725.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___151_10725.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___151_10725.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___151_10725.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___151_10725.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___151_10725.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___151_10725.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___151_10725.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___151_10725.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___151_10725.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___151_10725.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___151_10725.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___151_10725.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___151_10725.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10746 = FStar_Syntax_Util.abs_formals e in
                match uu____10746 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10795::uu____10796 ->
                         let uu____10804 =
                           let uu____10805 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10805.FStar_Syntax_Syntax.n in
                         (match uu____10804 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10832 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10832 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10858 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10858
                                   then
                                     let uu____10876 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____10876 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____10922  ->
                                                   fun uu____10923  ->
                                                     match (uu____10922,
                                                             uu____10923)
                                                     with
                                                     | ((x,uu____10933),
                                                        (b,uu____10935)) ->
                                                         let uu____10940 =
                                                           let uu____10945 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____10945) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____10940)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____10947 =
                                            let uu____10958 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____10958) in
                                          (uu____10947, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____10993 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____10993 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11045) ->
                              let uu____11050 =
                                let uu____11061 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11061 in
                              (uu____11050, true)
                          | uu____11094 when Prims.op_Negation norm1 ->
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
                          | uu____11096 ->
                              let uu____11097 =
                                let uu____11098 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11099 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11098
                                  uu____11099 in
                              failwith uu____11097)
                     | uu____11112 ->
                         let uu____11113 =
                           let uu____11114 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11114.FStar_Syntax_Syntax.n in
                         (match uu____11113 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11141 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11141 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11159 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11159 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11207 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11235 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11235
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11242 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11283  ->
                            fun lb  ->
                              match uu____11283 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11334 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11334
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11337 =
                                      let uu____11345 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11345
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11337 with
                                    | (tok,decl,env2) ->
                                        let uu____11370 =
                                          let uu____11377 =
                                            let uu____11383 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11383, tok) in
                                          uu____11377 :: toks in
                                        (uu____11370, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11242 with
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
                        | uu____11485 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11490 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11490 vars)
                            else
                              (let uu____11492 =
                                 let uu____11496 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11496) in
                               FStar_SMTEncoding_Util.mkApp uu____11492) in
                      let uu____11501 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___119_11503  ->
                                 match uu___119_11503 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11504 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11507 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11507))) in
                      if uu____11501
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11527;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11529;
                                FStar_Syntax_Syntax.lbeff = uu____11530;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11571 =
                                 let uu____11575 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11575 with
                                 | (tcenv',uu____11586,e_t) ->
                                     let uu____11590 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11597 -> failwith "Impossible" in
                                     (match uu____11590 with
                                      | (e1,t_norm1) ->
                                          ((let uu___154_11606 = env1 in
                                            {
                                              bindings =
                                                (uu___154_11606.bindings);
                                              depth = (uu___154_11606.depth);
                                              tcenv = tcenv';
                                              warn = (uu___154_11606.warn);
                                              cache = (uu___154_11606.cache);
                                              nolabels =
                                                (uu___154_11606.nolabels);
                                              use_fuel_instrumented_version =
                                                (uu___154_11606.use_fuel_instrumented_version);
                                              encode_non_total_function_typ =
                                                (uu___154_11606.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___154_11606.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11571 with
                                | (env',e1,t_norm1) ->
                                    let uu____11613 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11613 with
                                     | ((binders,body,uu____11625,uu____11626),curry)
                                         ->
                                         ((let uu____11633 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11633
                                           then
                                             let uu____11634 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11635 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11634 uu____11635
                                           else ());
                                          (let uu____11637 =
                                             encode_binders None binders env' in
                                           match uu____11637 with
                                           | (vars,guards,env'1,binder_decls,uu____11653)
                                               ->
                                               let body1 =
                                                 let uu____11661 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11661
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11664 =
                                                 let uu____11669 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11669
                                                 then
                                                   let uu____11675 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11676 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11675, uu____11676)
                                                 else
                                                   (let uu____11682 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11682)) in
                                               (match uu____11664 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11696 =
                                                        let uu____11700 =
                                                          let uu____11701 =
                                                            let uu____11707 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11707) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11701 in
                                                        let uu____11713 =
                                                          let uu____11715 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11715 in
                                                        (uu____11700,
                                                          uu____11713,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11696 in
                                                    let uu____11717 =
                                                      let uu____11719 =
                                                        let uu____11721 =
                                                          let uu____11723 =
                                                            let uu____11725 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11725 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11723 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11721 in
                                                      FStar_List.append
                                                        decls1 uu____11719 in
                                                    (uu____11717, env1))))))
                           | uu____11728 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11747 = varops.fresh "fuel" in
                             (uu____11747, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let s_fuel_tm =
                             FStar_SMTEncoding_Util.mkApp
                               ("SFuel", [fuel_tm]) in
                           let env0 = env1 in
                           let uu____11752 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11791  ->
                                     fun uu____11792  ->
                                       match (uu____11791, uu____11792) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____11874 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____11874 in
                                           let gtok =
                                             let uu____11876 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____11876 in
                                           let env3 =
                                             let uu____11878 =
                                               let uu____11880 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [s_fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____11880 in
                                             push_free_var env2 flid gtok
                                               uu____11878 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11752 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____11966
                                 t_norm uu____11968 =
                                 match (uu____11966, uu____11968) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____11995;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____11996;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12013 =
                                       let uu____12017 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12017 with
                                       | (tcenv',uu____12032,e_t) ->
                                           let uu____12036 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12043 ->
                                                 failwith "Impossible" in
                                           (match uu____12036 with
                                            | (e1,t_norm1) ->
                                                ((let uu___155_12052 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___155_12052.bindings);
                                                    depth =
                                                      (uu___155_12052.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___155_12052.warn);
                                                    cache =
                                                      (uu___155_12052.cache);
                                                    nolabels =
                                                      (uu___155_12052.nolabels);
                                                    use_fuel_instrumented_version
                                                      =
                                                      (uu___155_12052.use_fuel_instrumented_version);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___155_12052.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___155_12052.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12013 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12062 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12062
                                            then
                                              let uu____12063 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12064 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12065 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12063 uu____12064
                                                uu____12065
                                            else ());
                                           (let uu____12067 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12067 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12089 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12089
                                                  then
                                                    let uu____12090 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12091 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12092 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12093 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12090 uu____12091
                                                      uu____12092 uu____12093
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12097 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12097 with
                                                  | (vars,guards,env'1,binder_decls,uu____12115)
                                                      ->
                                                      let decl_g =
                                                        let uu____12123 =
                                                          let uu____12129 =
                                                            let uu____12131 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12131 in
                                                          (g, uu____12129,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12123 in
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
                                                        let uu____12146 =
                                                          let uu____12150 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12150) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12146 in
                                                      let gss_app =
                                                        let uu____12156 =
                                                          let uu____12160 =
                                                            let uu____12162 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [s_fuel_tm]) in
                                                            uu____12162 ::
                                                              vars_tm in
                                                          (g, uu____12160) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12156 in
                                                      let gmax =
                                                        let uu____12166 =
                                                          let uu____12170 =
                                                            let uu____12172 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12172 ::
                                                              vars_tm in
                                                          (g, uu____12170) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12166 in
                                                      let body1 =
                                                        let uu____12176 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12176
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12178 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12178 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12189
                                                               =
                                                               let uu____12193
                                                                 =
                                                                 let uu____12194
                                                                   =
                                                                   let uu____12202
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
                                                                    uu____12202) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12194 in
                                                               let uu____12213
                                                                 =
                                                                 let uu____12215
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12215 in
                                                               (uu____12193,
                                                                 uu____12213,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12189 in
                                                           let eqn_f =
                                                             let uu____12218
                                                               =
                                                               let uu____12222
                                                                 =
                                                                 let uu____12223
                                                                   =
                                                                   let uu____12229
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12229) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12223 in
                                                               (uu____12222,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12218 in
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
                                                             let uu____12241
                                                               =
                                                               let uu____12245
                                                                 =
                                                                 let uu____12246
                                                                   =
                                                                   let uu____12252
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gs_app,
                                                                    g_app) in
                                                                   ([
                                                                    [gs_app]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12252) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12246 in
                                                               (uu____12245,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12241 in
                                                           let uu____12263 =
                                                             let uu____12268
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12268
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12285)
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
                                                                    let uu____12300
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12300
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12303
                                                                    =
                                                                    let uu____12307
                                                                    =
                                                                    let uu____12308
                                                                    =
                                                                    let uu____12314
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12314) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12308 in
                                                                    (uu____12307,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12303 in
                                                                 let uu____12325
                                                                   =
                                                                   let uu____12329
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12329
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12337
                                                                    =
                                                                    let uu____12339
                                                                    =
                                                                    let uu____12340
                                                                    =
                                                                    let uu____12344
                                                                    =
                                                                    let uu____12345
                                                                    =
                                                                    let uu____12351
                                                                    =
                                                                    let uu____12352
                                                                    =
                                                                    let uu____12355
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12355,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12352 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12351) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12345 in
                                                                    (uu____12344,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12340 in
                                                                    [uu____12339] in
                                                                    (d3,
                                                                    uu____12337) in
                                                                 (match uu____12325
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12263
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
                               let uu____12390 =
                                 let uu____12397 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12433  ->
                                      fun uu____12434  ->
                                        match (uu____12433, uu____12434) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12520 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12520 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12397 in
                               (match uu____12390 with
                                | (decls2,eqns,env01) ->
                                    let uu____12560 =
                                      let isDeclFun uu___120_12568 =
                                        match uu___120_12568 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12569 -> true
                                        | uu____12575 -> false in
                                      let uu____12576 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12576
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12560 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12603 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12603
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
        let uu____12636 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12636 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12639 = encode_sigelt' env se in
      match uu____12639 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12649 =
                  let uu____12650 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12650 in
                [uu____12649]
            | uu____12651 ->
                let uu____12652 =
                  let uu____12654 =
                    let uu____12655 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12655 in
                  uu____12654 :: g in
                let uu____12656 =
                  let uu____12658 =
                    let uu____12659 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12659 in
                  [uu____12658] in
                FStar_List.append uu____12652 uu____12656 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12667 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12676 =
            let uu____12677 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12677 Prims.op_Negation in
          if uu____12676
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12697 ->
                   let uu____12698 =
                     let uu____12701 =
                       let uu____12702 =
                         let uu____12717 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12717) in
                       FStar_Syntax_Syntax.Tm_abs uu____12702 in
                     FStar_Syntax_Syntax.mk uu____12701 in
                   uu____12698 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12770 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12770 with
               | (aname,atok,env2) ->
                   let uu____12780 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12780 with
                    | (formals,uu____12790) ->
                        let uu____12797 =
                          let uu____12800 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12800 env2 in
                        (match uu____12797 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12808 =
                                 let uu____12809 =
                                   let uu____12815 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12823  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12815,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12809 in
                               [uu____12808;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12830 =
                               let aux uu____12859 uu____12860 =
                                 match (uu____12859, uu____12860) with
                                 | ((bv,uu____12887),(env3,acc_sorts,acc)) ->
                                     let uu____12908 = gen_term_var env3 bv in
                                     (match uu____12908 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12830 with
                              | (uu____12946,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____12960 =
                                      let uu____12964 =
                                        let uu____12965 =
                                          let uu____12971 =
                                            let uu____12972 =
                                              let uu____12975 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____12975) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12972 in
                                          ([[app]], xs_sorts, uu____12971) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12965 in
                                      (uu____12964, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12960 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____12987 =
                                      let uu____12991 =
                                        let uu____12992 =
                                          let uu____12998 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____12998) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12992 in
                                      (uu____12991,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12987 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13008 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13008 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13024,uu____13025)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13026 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13026 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13037,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13042 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___121_13044  ->
                      match uu___121_13044 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13047 -> false)) in
            Prims.op_Negation uu____13042 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13053 = encode_top_level_val env fv t quals in
             match uu____13053 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13065 =
                   let uu____13067 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13067 in
                 (uu____13065, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13072 = encode_formula f env in
          (match uu____13072 with
           | (f1,decls) ->
               let g =
                 let uu____13081 =
                   let uu____13082 =
                     let uu____13086 =
                       let uu____13088 =
                         let uu____13089 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13089 in
                       Some uu____13088 in
                     let uu____13090 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13086, uu____13090) in
                   FStar_SMTEncoding_Util.mkAssume uu____13082 in
                 [uu____13081] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13094,uu____13095) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13101 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13108 =
                       let uu____13113 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13113.FStar_Syntax_Syntax.fv_name in
                     uu____13108.FStar_Syntax_Syntax.v in
                   let uu____13117 =
                     let uu____13118 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13118 in
                   if uu____13117
                   then
                     let val_decl =
                       let uu___156_13133 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___156_13133.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___156_13133.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___156_13133.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13137 = encode_sigelt' env1 val_decl in
                     match uu____13137 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13101 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13154,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13156;
                          FStar_Syntax_Syntax.lbtyp = uu____13157;
                          FStar_Syntax_Syntax.lbeff = uu____13158;
                          FStar_Syntax_Syntax.lbdef = uu____13159;_}::[]),uu____13160,uu____13161)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13175 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13175 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13198 =
                   let uu____13200 =
                     let uu____13201 =
                       let uu____13205 =
                         let uu____13206 =
                           let uu____13212 =
                             let uu____13213 =
                               let uu____13216 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13216) in
                             FStar_SMTEncoding_Util.mkEq uu____13213 in
                           ([[b2t_x]], [xx], uu____13212) in
                         FStar_SMTEncoding_Util.mkForall uu____13206 in
                       (uu____13205, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13201 in
                   [uu____13200] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13198 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13233,uu____13234,uu____13235)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13241  ->
                  match uu___122_13241 with
                  | FStar_Syntax_Syntax.Discriminator uu____13242 -> true
                  | uu____13243 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13245,lids,uu____13247) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13254 =
                     let uu____13255 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13255.FStar_Ident.idText in
                   uu____13254 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___123_13257  ->
                     match uu___123_13257 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13258 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13261,uu____13262)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___124_13272  ->
                  match uu___124_13272 with
                  | FStar_Syntax_Syntax.Projector uu____13273 -> true
                  | uu____13276 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13283 = try_lookup_free_var env l in
          (match uu____13283 with
           | Some uu____13287 -> ([], env)
           | None  ->
               let se1 =
                 let uu___157_13290 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___157_13290.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___157_13290.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13296,uu____13297) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13309) ->
          let uu____13314 = encode_sigelts env ses in
          (match uu____13314 with
           | (g,env1) ->
               let uu____13324 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___125_13334  ->
                         match uu___125_13334 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13335;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13336;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13337;_}
                             -> false
                         | uu____13339 -> true)) in
               (match uu____13324 with
                | (g',inversions) ->
                    let uu____13348 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___126_13358  ->
                              match uu___126_13358 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13359 ->
                                  true
                              | uu____13365 -> false)) in
                    (match uu____13348 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13376,tps,k,uu____13379,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___127_13389  ->
                    match uu___127_13389 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13390 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13397 = c in
              match uu____13397 with
              | (name,args,uu____13401,uu____13402,uu____13403) ->
                  let uu____13406 =
                    let uu____13407 =
                      let uu____13413 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13420  ->
                                match uu____13420 with
                                | (uu____13424,sort,uu____13426) -> sort)) in
                      (name, uu____13413, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13407 in
                  [uu____13406]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13444 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13447 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13447 FStar_Option.isNone)) in
            if uu____13444
            then []
            else
              (let uu____13464 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13464 with
               | (xxsym,xx) ->
                   let uu____13470 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13481  ->
                             fun l  ->
                               match uu____13481 with
                               | (out,decls) ->
                                   let uu____13493 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13493 with
                                    | (uu____13499,data_t) ->
                                        let uu____13501 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13501 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13530 =
                                                 let uu____13531 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13531.FStar_Syntax_Syntax.n in
                                               match uu____13530 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13539,indices) ->
                                                   indices
                                               | uu____13555 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13567  ->
                                                         match uu____13567
                                                         with
                                                         | (x,uu____13571) ->
                                                             let uu____13572
                                                               =
                                                               let uu____13573
                                                                 =
                                                                 let uu____13577
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13577,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13573 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13572)
                                                    env) in
                                             let uu____13579 =
                                               encode_args indices env1 in
                                             (match uu____13579 with
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
                                                      let uu____13599 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13607
                                                                 =
                                                                 let uu____13610
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13610,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13607)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13599
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13612 =
                                                      let uu____13613 =
                                                        let uu____13616 =
                                                          let uu____13617 =
                                                            let uu____13620 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13620,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13617 in
                                                        (out, uu____13616) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13613 in
                                                    (uu____13612,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13470 with
                    | (data_ax,decls) ->
                        let uu____13628 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13628 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13639 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13639 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13642 =
                                 let uu____13646 =
                                   let uu____13647 =
                                     let uu____13653 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13661 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13653,
                                       uu____13661) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13647 in
                                 let uu____13669 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13646, (Some "inversion axiom"),
                                   uu____13669) in
                               FStar_SMTEncoding_Util.mkAssume uu____13642 in
                             let pattern_guarded_inversion =
                               let uu____13673 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13673
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13681 =
                                   let uu____13682 =
                                     let uu____13686 =
                                       let uu____13687 =
                                         let uu____13693 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13701 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13693, uu____13701) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13687 in
                                     let uu____13709 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13686, (Some "inversion axiom"),
                                       uu____13709) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13682 in
                                 [uu____13681]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13712 =
            let uu____13720 =
              let uu____13721 = FStar_Syntax_Subst.compress k in
              uu____13721.FStar_Syntax_Syntax.n in
            match uu____13720 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13750 -> (tps, k) in
          (match uu____13712 with
           | (formals,res) ->
               let uu____13765 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13765 with
                | (formals1,res1) ->
                    let uu____13772 = encode_binders None formals1 env in
                    (match uu____13772 with
                     | (vars,guards,env',binder_decls,uu____13787) ->
                         let uu____13794 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13794 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13807 =
                                  let uu____13811 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13811) in
                                FStar_SMTEncoding_Util.mkApp uu____13807 in
                              let uu____13816 =
                                let tname_decl =
                                  let uu____13822 =
                                    let uu____13823 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13838  ->
                                              match uu____13838 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13846 = varops.next_id () in
                                    (tname, uu____13823,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13846, false) in
                                  constructor_or_logic_type_decl uu____13822 in
                                let uu____13851 =
                                  match vars with
                                  | [] ->
                                      let uu____13858 =
                                        let uu____13859 =
                                          let uu____13861 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13861 in
                                        push_free_var env1 t tname
                                          uu____13859 in
                                      ([], uu____13858)
                                  | uu____13865 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13871 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13871 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13880 =
                                          let uu____13884 =
                                            let uu____13885 =
                                              let uu____13893 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13893) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13885 in
                                          (uu____13884,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13880 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13851 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13816 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13916 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____13916 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13930 =
                                               let uu____13931 =
                                                 let uu____13935 =
                                                   let uu____13936 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13936 in
                                                 (uu____13935,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13931 in
                                             [uu____13930]
                                           else [] in
                                         let uu____13939 =
                                           let uu____13941 =
                                             let uu____13943 =
                                               let uu____13944 =
                                                 let uu____13948 =
                                                   let uu____13949 =
                                                     let uu____13955 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____13955) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____13949 in
                                                 (uu____13948, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13944 in
                                             [uu____13943] in
                                           FStar_List.append karr uu____13941 in
                                         FStar_List.append decls1 uu____13939 in
                                   let aux =
                                     let uu____13964 =
                                       let uu____13966 =
                                         inversion_axioms tapp vars in
                                       let uu____13968 =
                                         let uu____13970 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____13970] in
                                       FStar_List.append uu____13966
                                         uu____13968 in
                                     FStar_List.append kindingAx uu____13964 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13975,uu____13976,uu____13977,uu____13978,uu____13979)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13984,t,uu____13986,n_tps,uu____13988) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____13993 = new_term_constant_and_tok_from_lid env d in
          (match uu____13993 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14004 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14004 with
                | (formals,t_res) ->
                    let uu____14026 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14026 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14035 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14035 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14073 =
                                            mk_term_projector_name d x in
                                          (uu____14073,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14075 =
                                  let uu____14085 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14085, true) in
                                FStar_All.pipe_right uu____14075
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
                              let uu____14107 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14107 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14115::uu____14116 ->
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
                                         let uu____14141 =
                                           let uu____14147 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14147) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14141
                                     | uu____14160 -> tok_typing in
                                   let uu____14165 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14165 with
                                    | (vars',guards',env'',decls_formals,uu____14180)
                                        ->
                                        let uu____14187 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14187 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14206 ->
                                                   let uu____14210 =
                                                     let uu____14211 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14211 in
                                                   [uu____14210] in
                                             let encode_elim uu____14218 =
                                               let uu____14219 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14219 with
                                               | (head1,args) ->
                                                   let uu____14248 =
                                                     let uu____14249 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14249.FStar_Syntax_Syntax.n in
                                                   (match uu____14248 with
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
                                                        let uu____14267 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14267
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
                                                                 | uu____14293
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14301
                                                                    =
                                                                    let uu____14302
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14302 in
                                                                    if
                                                                    uu____14301
                                                                    then
                                                                    let uu____14309
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14309]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14311
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14324
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14324
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14346
                                                                    =
                                                                    let uu____14350
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14350 in
                                                                    (match uu____14346
                                                                    with
                                                                    | 
                                                                    (uu____14357,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14363
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14363
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14365
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14365
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
                                                             (match uu____14311
                                                              with
                                                              | (uu____14373,arg_vars,elim_eqns_or_guards,uu____14376)
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
                                                                    let uu____14395
                                                                    =
                                                                    let uu____14399
                                                                    =
                                                                    let uu____14400
                                                                    =
                                                                    let uu____14406
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14412
                                                                    =
                                                                    let uu____14413
                                                                    =
                                                                    let uu____14416
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14416) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14413 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14406,
                                                                    uu____14412) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14400 in
                                                                    (uu____14399,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14395 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14429
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14429,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14431
                                                                    =
                                                                    let uu____14435
                                                                    =
                                                                    let uu____14436
                                                                    =
                                                                    let uu____14442
                                                                    =
                                                                    let uu____14445
                                                                    =
                                                                    let uu____14447
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14447] in
                                                                    [uu____14445] in
                                                                    let uu____14450
                                                                    =
                                                                    let uu____14451
                                                                    =
                                                                    let uu____14454
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14455
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14454,
                                                                    uu____14455) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14451 in
                                                                    (uu____14442,
                                                                    [x],
                                                                    uu____14450) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14436 in
                                                                    let uu____14465
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14435,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14465) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14431
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14470
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
                                                                    (let uu____14485
                                                                    =
                                                                    let uu____14486
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14486
                                                                    dapp1 in
                                                                    [uu____14485]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14470
                                                                    FStar_List.flatten in
                                                                    let uu____14490
                                                                    =
                                                                    let uu____14494
                                                                    =
                                                                    let uu____14495
                                                                    =
                                                                    let uu____14501
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14507
                                                                    =
                                                                    let uu____14508
                                                                    =
                                                                    let uu____14511
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14511) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14508 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14501,
                                                                    uu____14507) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14495 in
                                                                    (uu____14494,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14490) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14521 ->
                                                        ((let uu____14523 =
                                                            let uu____14524 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14525 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14524
                                                              uu____14525 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14523);
                                                         ([], []))) in
                                             let uu____14528 = encode_elim () in
                                             (match uu____14528 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14540 =
                                                      let uu____14542 =
                                                        let uu____14544 =
                                                          let uu____14546 =
                                                            let uu____14548 =
                                                              let uu____14549
                                                                =
                                                                let uu____14555
                                                                  =
                                                                  let uu____14557
                                                                    =
                                                                    let uu____14558
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14558 in
                                                                  Some
                                                                    uu____14557 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14555) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14549 in
                                                            [uu____14548] in
                                                          let uu____14561 =
                                                            let uu____14563 =
                                                              let uu____14565
                                                                =
                                                                let uu____14567
                                                                  =
                                                                  let uu____14569
                                                                    =
                                                                    let uu____14571
                                                                    =
                                                                    let uu____14573
                                                                    =
                                                                    let uu____14574
                                                                    =
                                                                    let uu____14578
                                                                    =
                                                                    let uu____14579
                                                                    =
                                                                    let uu____14585
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14585) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14579 in
                                                                    (uu____14578,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14574 in
                                                                    let uu____14592
                                                                    =
                                                                    let uu____14594
                                                                    =
                                                                    let uu____14595
                                                                    =
                                                                    let uu____14599
                                                                    =
                                                                    let uu____14600
                                                                    =
                                                                    let uu____14606
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14612
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14606,
                                                                    uu____14612) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14600 in
                                                                    (uu____14599,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14595 in
                                                                    [uu____14594] in
                                                                    uu____14573
                                                                    ::
                                                                    uu____14592 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14571 in
                                                                  FStar_List.append
                                                                    uu____14569
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14567 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14565 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14563 in
                                                          FStar_List.append
                                                            uu____14546
                                                            uu____14561 in
                                                        FStar_List.append
                                                          decls3 uu____14544 in
                                                      FStar_List.append
                                                        decls2 uu____14542 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14540 in
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
           (fun uu____14633  ->
              fun se  ->
                match uu____14633 with
                | (g,env1) ->
                    let uu____14645 = encode_sigelt env1 se in
                    (match uu____14645 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14681 =
        match uu____14681 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14699 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14704 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14704
                   then
                     let uu____14705 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14706 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14707 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14705 uu____14706 uu____14707
                   else ());
                  (let uu____14709 = encode_term t1 env1 in
                   match uu____14709 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14719 =
                         let uu____14723 =
                           let uu____14724 =
                             let uu____14725 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14725
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14724 in
                         new_term_constant_from_string env1 x uu____14723 in
                       (match uu____14719 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14736 = FStar_Options.log_queries () in
                              if uu____14736
                              then
                                let uu____14738 =
                                  let uu____14739 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14740 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14741 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14739 uu____14740 uu____14741 in
                                Some uu____14738
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14752,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14761 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14761 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14780 = encode_sigelt env1 se in
                 (match uu____14780 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14790 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14790 with | (uu____14802,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14847  ->
            match uu____14847 with
            | (l,uu____14854,uu____14855) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14876  ->
            match uu____14876 with
            | (l,uu____14884,uu____14885) ->
                let uu____14890 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____14891 =
                  let uu____14893 =
                    let uu____14894 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14894 in
                  [uu____14893] in
                uu____14890 :: uu____14891)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14905 =
      let uu____14907 =
        let uu____14908 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____14910 =
          let uu____14911 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____14911 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14908;
          nolabels = false;
          use_fuel_instrumented_version = None;
          encode_non_total_function_typ = true;
          current_module_name = uu____14910
        } in
      [uu____14907] in
    FStar_ST.write last_env uu____14905
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____14921 = FStar_ST.read last_env in
      match uu____14921 with
      | [] -> failwith "No env; call init first!"
      | e::uu____14927 ->
          let uu___158_14929 = e in
          let uu____14930 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___158_14929.bindings);
            depth = (uu___158_14929.depth);
            tcenv;
            warn = (uu___158_14929.warn);
            cache = (uu___158_14929.cache);
            nolabels = (uu___158_14929.nolabels);
            use_fuel_instrumented_version =
              (uu___158_14929.use_fuel_instrumented_version);
            encode_non_total_function_typ =
              (uu___158_14929.encode_non_total_function_typ);
            current_module_name = uu____14930
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____14934 = FStar_ST.read last_env in
    match uu____14934 with
    | [] -> failwith "Empty env stack"
    | uu____14939::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____14947  ->
    let uu____14948 = FStar_ST.read last_env in
    match uu____14948 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___159_14959 = hd1 in
          {
            bindings = (uu___159_14959.bindings);
            depth = (uu___159_14959.depth);
            tcenv = (uu___159_14959.tcenv);
            warn = (uu___159_14959.warn);
            cache = refs;
            nolabels = (uu___159_14959.nolabels);
            use_fuel_instrumented_version =
              (uu___159_14959.use_fuel_instrumented_version);
            encode_non_total_function_typ =
              (uu___159_14959.encode_non_total_function_typ);
            current_module_name = (uu___159_14959.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____14965  ->
    let uu____14966 = FStar_ST.read last_env in
    match uu____14966 with
    | [] -> failwith "Popping an empty stack"
    | uu____14971::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____14979  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____14982  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____14985  ->
    let uu____14986 = FStar_ST.read last_env in
    match uu____14986 with
    | hd1::uu____14992::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____14998 -> failwith "Impossible"
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
        | (uu____15047::uu____15048,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___160_15052 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___160_15052.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___160_15052.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___160_15052.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15053 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15064 =
        let uu____15066 =
          let uu____15067 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15067 in
        let uu____15068 = open_fact_db_tags env in uu____15066 :: uu____15068 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15064
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
      let uu____15083 = encode_sigelt env se in
      match uu____15083 with
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
        let uu____15108 = FStar_Options.log_queries () in
        if uu____15108
        then
          let uu____15110 =
            let uu____15111 =
              let uu____15112 =
                let uu____15113 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15113 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15112 in
            FStar_SMTEncoding_Term.Caption uu____15111 in
          uu____15110 :: decls
        else decls in
      let env =
        let uu____15120 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15120 tcenv in
      let uu____15121 = encode_top_level_facts env se in
      match uu____15121 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15130 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15130))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15141 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15141
       then
         let uu____15142 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15142
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15163  ->
                 fun se  ->
                   match uu____15163 with
                   | (g,env2) ->
                       let uu____15175 = encode_top_level_facts env2 se in
                       (match uu____15175 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15188 =
         encode_signature
           (let uu___161_15192 = env in
            {
              bindings = (uu___161_15192.bindings);
              depth = (uu___161_15192.depth);
              tcenv = (uu___161_15192.tcenv);
              warn = false;
              cache = (uu___161_15192.cache);
              nolabels = (uu___161_15192.nolabels);
              use_fuel_instrumented_version =
                (uu___161_15192.use_fuel_instrumented_version);
              encode_non_total_function_typ =
                (uu___161_15192.encode_non_total_function_typ);
              current_module_name = (uu___161_15192.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15188 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15204 = FStar_Options.log_queries () in
             if uu____15204
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___162_15209 = env1 in
               {
                 bindings = (uu___162_15209.bindings);
                 depth = (uu___162_15209.depth);
                 tcenv = (uu___162_15209.tcenv);
                 warn = true;
                 cache = (uu___162_15209.cache);
                 nolabels = (uu___162_15209.nolabels);
                 use_fuel_instrumented_version =
                   (uu___162_15209.use_fuel_instrumented_version);
                 encode_non_total_function_typ =
                   (uu___162_15209.encode_non_total_function_typ);
                 current_module_name = (uu___162_15209.current_module_name)
               });
            (let uu____15211 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15211
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
        (let uu____15246 =
           let uu____15247 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15247.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15246);
        (let env =
           let uu____15249 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15249 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15256 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15277 = aux rest in
                 (match uu____15277 with
                  | (out,rest1) ->
                      let t =
                        let uu____15295 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15295 with
                        | Some uu____15299 ->
                            let uu____15300 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15300
                              x.FStar_Syntax_Syntax.sort
                        | uu____15301 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15304 =
                        let uu____15306 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___163_15307 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___163_15307.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___163_15307.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15306 :: out in
                      (uu____15304, rest1))
             | uu____15310 -> ([], bindings1) in
           let uu____15314 = aux bindings in
           match uu____15314 with
           | (closing,bindings1) ->
               let uu____15328 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15328, bindings1) in
         match uu____15256 with
         | (q1,bindings1) ->
             let uu____15341 =
               let uu____15344 =
                 FStar_List.filter
                   (fun uu___128_15346  ->
                      match uu___128_15346 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15347 ->
                          false
                      | uu____15351 -> true) bindings1 in
               encode_env_bindings env uu____15344 in
             (match uu____15341 with
              | (env_decls,env1) ->
                  ((let uu____15362 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15362
                    then
                      let uu____15363 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15363
                    else ());
                   (let uu____15365 = encode_formula q1 env1 in
                    match uu____15365 with
                    | (phi,qdecls) ->
                        let uu____15377 =
                          let uu____15380 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15380 phi in
                        (match uu____15377 with
                         | (labels,phi1) ->
                             let uu____15390 = encode_labels labels in
                             (match uu____15390 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15411 =
                                      let uu____15415 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15416 =
                                        varops.mk_unique "@query" in
                                      (uu____15415, (Some "query"),
                                        uu____15416) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15411 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15429 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15429 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15431 = encode_formula q env in
       match uu____15431 with
       | (f,uu____15435) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15437) -> true
             | uu____15440 -> false)))