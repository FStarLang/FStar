open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___103_74  ->
       match uu___103_74 with
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
        let uu___128_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___128_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___128_140.FStar_Syntax_Syntax.sort)
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
    let uu___129_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___129_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___129_780.FStar_Syntax_Syntax.sort)
    }
type binding =
  | Binding_var of (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term)
  | Binding_fvar of (FStar_Ident.lident* Prims.string*
  FStar_SMTEncoding_Term.term Prims.option* FStar_SMTEncoding_Term.term
  Prims.option)
let uu___is_Binding_var: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_var _0 -> true | uu____802 -> false
let __proj__Binding_var__item___0:
  binding -> (FStar_Syntax_Syntax.bv* FStar_SMTEncoding_Term.term) =
  fun projectee  -> match projectee with | Binding_var _0 -> _0
let uu___is_Binding_fvar: binding -> Prims.bool =
  fun projectee  ->
    match projectee with | Binding_fvar _0 -> true | uu____826 -> false
let __proj__Binding_fvar__item___0:
  binding ->
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term
      Prims.option* FStar_SMTEncoding_Term.term Prims.option)
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
  use_zfuel_name: Prims.bool;
  encode_non_total_function_typ: Prims.bool;
  current_module_name: Prims.string;}
let mk_cache_entry env tsym cvar_sorts t_decls =
  let names1 =
    FStar_All.pipe_right t_decls
      (FStar_List.collect
         (fun uu___104_1001  ->
            match uu___104_1001 with
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
           (fun uu___105_1016  ->
              match uu___105_1016 with
              | Binding_var (x,uu____1018) ->
                  FStar_Syntax_Print.bv_to_string x
              | Binding_fvar (l,uu____1020,uu____1021,uu____1022) ->
                  FStar_Syntax_Print.lid_to_string l)) in
    FStar_All.pipe_right uu____1012 (FStar_String.concat ", ")
let lookup_binding env f = FStar_Util.find_map env.bindings f
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string Prims.option
  =
  fun env  ->
    fun t  ->
      let uu____1055 =
        FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
      if uu____1055
      then
        let uu____1057 = FStar_Syntax_Print.term_to_string t in
        Some uu____1057
      else None
let fresh_fvar:
  Prims.string ->
    FStar_SMTEncoding_Term.sort ->
      (Prims.string* FStar_SMTEncoding_Term.term)
  =
  fun x  ->
    fun s  ->
      let xsym = varops.fresh x in
      let uu____1068 = FStar_SMTEncoding_Util.mkFreeV (xsym, s) in
      (xsym, uu____1068)
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
        (let uu___130_1080 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___130_1080.tcenv);
           warn = (uu___130_1080.warn);
           cache = (uu___130_1080.cache);
           nolabels = (uu___130_1080.nolabels);
           use_zfuel_name = (uu___130_1080.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___130_1080.encode_non_total_function_typ);
           current_module_name = (uu___130_1080.current_module_name)
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
        (let uu___131_1093 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___131_1093.depth);
           tcenv = (uu___131_1093.tcenv);
           warn = (uu___131_1093.warn);
           cache = (uu___131_1093.cache);
           nolabels = (uu___131_1093.nolabels);
           use_zfuel_name = (uu___131_1093.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___131_1093.encode_non_total_function_typ);
           current_module_name = (uu___131_1093.current_module_name)
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
          (let uu___132_1109 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___132_1109.depth);
             tcenv = (uu___132_1109.tcenv);
             warn = (uu___132_1109.warn);
             cache = (uu___132_1109.cache);
             nolabels = (uu___132_1109.nolabels);
             use_zfuel_name = (uu___132_1109.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___132_1109.encode_non_total_function_typ);
             current_module_name = (uu___132_1109.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___133_1119 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___133_1119.depth);
          tcenv = (uu___133_1119.tcenv);
          warn = (uu___133_1119.warn);
          cache = (uu___133_1119.cache);
          nolabels = (uu___133_1119.nolabels);
          use_zfuel_name = (uu___133_1119.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___133_1119.encode_non_total_function_typ);
          current_module_name = (uu___133_1119.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___106_1135  ->
             match uu___106_1135 with
             | Binding_var (b,t) when FStar_Syntax_Syntax.bv_eq b a' ->
                 Some (b, t)
             | uu____1143 -> None) in
      let uu____1146 = aux a in
      match uu____1146 with
      | None  ->
          let a2 = unmangle a in
          let uu____1153 = aux a2 in
          (match uu____1153 with
           | None  ->
               let uu____1159 =
                 let uu____1160 = FStar_Syntax_Print.bv_to_string a2 in
                 let uu____1161 = print_env env in
                 FStar_Util.format2
                   "Bound term variable not found (after unmangling): %s in environment: %s"
                   uu____1160 uu____1161 in
               failwith uu____1159
           | Some (b,t) -> t)
      | Some (b,t) -> t
let new_term_constant_and_tok_from_lid:
  env_t -> FStar_Ident.lident -> (Prims.string* Prims.string* env_t) =
  fun env  ->
    fun x  ->
      let fname = varops.new_fvar x in
      let ftok = Prims.strcat fname "@tok" in
      let uu____1181 =
        let uu___134_1182 = env in
        let uu____1183 =
          let uu____1185 =
            let uu____1186 =
              let uu____1193 =
                let uu____1195 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_28  -> Some _0_28) uu____1195 in
              (x, fname, uu____1193, None) in
            Binding_fvar uu____1186 in
          uu____1185 :: (env.bindings) in
        {
          bindings = uu____1183;
          depth = (uu___134_1182.depth);
          tcenv = (uu___134_1182.tcenv);
          warn = (uu___134_1182.warn);
          cache = (uu___134_1182.cache);
          nolabels = (uu___134_1182.nolabels);
          use_zfuel_name = (uu___134_1182.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___134_1182.encode_non_total_function_typ);
          current_module_name = (uu___134_1182.current_module_name)
        } in
      (fname, ftok, uu____1181)
let try_lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___107_1217  ->
           match uu___107_1217 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1239 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1251 =
        lookup_binding env
          (fun uu___108_1253  ->
             match uu___108_1253 with
             | Binding_fvar (b,t1,t2,t3) when b.FStar_Ident.str = s ->
                 Some ()
             | uu____1263 -> None) in
      FStar_All.pipe_right uu____1251 FStar_Option.isSome
let lookup_lid:
  env_t ->
    FStar_Ident.lident ->
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option)
  =
  fun env  ->
    fun a  ->
      let uu____1276 = try_lookup_lid env a in
      match uu____1276 with
      | None  ->
          let uu____1293 =
            let uu____1294 = FStar_Syntax_Print.lid_to_string a in
            FStar_Util.format1 "Name not found: %s" uu____1294 in
          failwith uu____1293
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
          let uu___135_1325 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___135_1325.depth);
            tcenv = (uu___135_1325.tcenv);
            warn = (uu___135_1325.warn);
            cache = (uu___135_1325.cache);
            nolabels = (uu___135_1325.nolabels);
            use_zfuel_name = (uu___135_1325.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___135_1325.encode_non_total_function_typ);
            current_module_name = (uu___135_1325.current_module_name)
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
            let uu___136_1360 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___136_1360.depth);
              tcenv = (uu___136_1360.tcenv);
              warn = (uu___136_1360.warn);
              cache = (uu___136_1360.cache);
              nolabels = (uu___136_1360.nolabels);
              use_zfuel_name = (uu___136_1360.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___136_1360.encode_non_total_function_typ);
              current_module_name = (uu___136_1360.current_module_name)
            }
let try_lookup_free_var:
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun l  ->
      let uu____1370 = try_lookup_lid env l in
      match uu____1370 with
      | None  -> None
      | Some (name,sym,zf_opt) ->
          (match zf_opt with
           | Some f when env.use_zfuel_name -> Some f
           | uu____1397 ->
               (match sym with
                | Some t ->
                    (match t.FStar_SMTEncoding_Term.tm with
                     | FStar_SMTEncoding_Term.App (uu____1402,fuel::[]) ->
                         let uu____1405 =
                           let uu____1406 =
                             let uu____1407 =
                               FStar_SMTEncoding_Term.fv_of_term fuel in
                             FStar_All.pipe_right uu____1407 Prims.fst in
                           FStar_Util.starts_with uu____1406 "fuel" in
                         if uu____1405
                         then
                           let uu____1409 =
                             let uu____1410 =
                               FStar_SMTEncoding_Util.mkFreeV
                                 (name, FStar_SMTEncoding_Term.Term_sort) in
                             FStar_SMTEncoding_Term.mk_ApplyTF uu____1410
                               fuel in
                           FStar_All.pipe_left (fun _0_29  -> Some _0_29)
                             uu____1409
                         else Some t
                     | uu____1413 -> Some t)
                | uu____1414 -> None))
let lookup_free_var env a =
  let uu____1432 = try_lookup_free_var env a.FStar_Syntax_Syntax.v in
  match uu____1432 with
  | Some t -> t
  | None  ->
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
       | Some
           { FStar_SMTEncoding_Term.tm = FStar_SMTEncoding_Term.App (g,zf);
             FStar_SMTEncoding_Term.freevars = uu____1506;
             FStar_SMTEncoding_Term.rng = uu____1507;_}
           when env.use_zfuel_name -> (g, zf)
       | uu____1515 ->
           (match sym with
            | None  -> ((FStar_SMTEncoding_Term.Var name), [])
            | Some sym1 ->
                (match sym1.FStar_SMTEncoding_Term.tm with
                 | FStar_SMTEncoding_Term.App (g,fuel::[]) -> (g, [fuel])
                 | uu____1529 -> ((FStar_SMTEncoding_Term.Var name), []))))
let tok_of_name:
  env_t -> Prims.string -> FStar_SMTEncoding_Term.term Prims.option =
  fun env  ->
    fun nm  ->
      FStar_Util.find_map env.bindings
        (fun uu___109_1538  ->
           match uu___109_1538 with
           | Binding_fvar (uu____1540,nm',tok,uu____1543) when nm = nm' ->
               tok
           | uu____1548 -> None)
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
          let uu____1669 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1669 FStar_Option.isNone
      | uu____1682 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1689 =
        let uu____1690 = FStar_Syntax_Util.un_uinst t in
        uu____1690.FStar_Syntax_Syntax.n in
      match uu____1689 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1693,uu____1694,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___110_1723  ->
                  match uu___110_1723 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1724 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1725,uu____1726,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1753 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1753 FStar_Option.isSome
      | uu____1766 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1773 = head_normal env t in
      if uu____1773
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
    let uu____1784 =
      let uu____1785 = FStar_Syntax_Syntax.null_binder t in [uu____1785] in
    let uu____1786 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1784 uu____1786 None
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
                    let uu____1813 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1813
                | s ->
                    let uu____1816 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1816) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___111_1828  ->
    match uu___111_1828 with
    | FStar_SMTEncoding_Term.Var "ApplyTT"|FStar_SMTEncoding_Term.Var
      "ApplyTF" -> true
    | uu____1829 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1857;
                       FStar_SMTEncoding_Term.rng = uu____1858;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1872) ->
              let uu____1877 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1887 -> false) args (FStar_List.rev xs)) in
              if uu____1877 then tok_of_name env f else None
          | (uu____1890,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1893 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1895 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1895)) in
              if uu____1893 then Some t else None
          | uu____1898 -> None in
        check_partial_applications body (FStar_List.rev vars)
let reify_body:
  FStar_TypeChecker_Env.env ->
    FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term
  =
  fun env  ->
    fun t  ->
      let tm = FStar_Syntax_Util.mk_reify t in
      let tm' =
        FStar_TypeChecker_Normalize.normalize
          [FStar_TypeChecker_Normalize.Beta;
          FStar_TypeChecker_Normalize.Reify;
          FStar_TypeChecker_Normalize.Eager_unfolding;
          FStar_TypeChecker_Normalize.EraseUniverses;
          FStar_TypeChecker_Normalize.AllowUnboundUniverses] env tm in
      (let uu____1913 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env)
           (FStar_Options.Other "SMTEncodingReify") in
       if uu____1913
       then
         let uu____1914 = FStar_Syntax_Print.term_to_string tm in
         let uu____1915 = FStar_Syntax_Print.term_to_string tm' in
         FStar_Util.print2 "Reified body %s \nto %s\n" uu____1914 uu____1915
       else ());
      tm'
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
    | uu____1997 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___112_2000  ->
    match uu___112_2000 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2002 =
          let uu____2006 =
            let uu____2008 =
              let uu____2009 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2009 in
            [uu____2008] in
          ("FStar.Char.Char", uu____2006) in
        FStar_SMTEncoding_Util.mkApp uu____2002
    | FStar_Const.Const_int (i,None ) ->
        let uu____2017 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2017
    | FStar_Const.Const_int (i,Some uu____2019) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2028) ->
        let uu____2031 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2031
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2035 =
          let uu____2036 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2036 in
        failwith uu____2035
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2055 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2063 ->
            let uu____2068 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2068
        | uu____2069 ->
            if norm1
            then let uu____2070 = whnf env t1 in aux false uu____2070
            else
              (let uu____2072 =
                 let uu____2073 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2074 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2073 uu____2074 in
               failwith uu____2072) in
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
    | uu____2095 ->
        let uu____2096 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2096)
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
        (let uu____2239 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2239
         then
           let uu____2240 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2240
         else ());
        (let uu____2242 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2278  ->
                   fun b  ->
                     match uu____2278 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2321 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2330 = gen_term_var env1 x in
                           match uu____2330 with
                           | (xxsym,xx,env') ->
                               let uu____2344 =
                                 let uu____2347 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2347 env1 xx in
                               (match uu____2344 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2321 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2242 with
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
          let uu____2435 = encode_term t env in
          match uu____2435 with
          | (t1,decls) ->
              let uu____2442 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2442, decls)
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
          let uu____2450 = encode_term t env in
          match uu____2450 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2459 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2459, decls)
               | Some f ->
                   let uu____2461 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2461, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2468 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2468
       then
         let uu____2469 = FStar_Syntax_Print.tag_of_term t in
         let uu____2470 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2471 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2469 uu____2470
           uu____2471
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2476 =
             let uu____2477 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2478 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2479 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2480 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2477
               uu____2478 uu____2479 uu____2480 in
           failwith uu____2476
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2484 =
             let uu____2485 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2485 in
           failwith uu____2484
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2490) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2520) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2529 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2529, [])
       | FStar_Syntax_Syntax.Tm_type uu____2535 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2538) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2544 = encode_const c in (uu____2544, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2559 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2559 with
            | (binders1,res) ->
                let uu____2566 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2566
                then
                  let uu____2569 = encode_binders None binders1 env in
                  (match uu____2569 with
                   | (vars,guards,env',decls,uu____2584) ->
                       let fsym =
                         let uu____2594 = varops.fresh "f" in
                         (uu____2594, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2597 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___137_2601 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___137_2601.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___137_2601.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___137_2601.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___137_2601.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___137_2601.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___137_2601.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___137_2601.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___137_2601.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___137_2601.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___137_2601.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___137_2601.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___137_2601.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___137_2601.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___137_2601.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___137_2601.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___137_2601.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___137_2601.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___137_2601.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___137_2601.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___137_2601.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___137_2601.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___137_2601.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___137_2601.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2597 with
                        | (pre_opt,res_t) ->
                            let uu____2608 =
                              encode_term_pred None res_t env' app in
                            (match uu____2608 with
                             | (res_pred,decls') ->
                                 let uu____2615 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2622 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2622, [])
                                   | Some pre ->
                                       let uu____2625 =
                                         encode_formula pre env' in
                                       (match uu____2625 with
                                        | (guard,decls0) ->
                                            let uu____2633 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2633, decls0)) in
                                 (match uu____2615 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2641 =
                                          let uu____2647 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2647) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2641 in
                                      let cvars =
                                        let uu____2657 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2657
                                          (FStar_List.filter
                                             (fun uu____2663  ->
                                                match uu____2663 with
                                                | (x,uu____2667) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2678 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2678 with
                                       | Some cache_entry ->
                                           let uu____2683 =
                                             let uu____2684 =
                                               let uu____2688 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2688) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2684 in
                                           (uu____2683,
                                             (use_cache_entry cache_entry))
                                       | None  ->
                                           let tsym =
                                             let uu____2699 =
                                               let uu____2700 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2700 in
                                             varops.mk_unique uu____2699 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2707 =
                                               FStar_Options.log_queries () in
                                             if uu____2707
                                             then
                                               let uu____2709 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2709
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2715 =
                                               let uu____2719 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2719) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2715 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2727 =
                                               let uu____2731 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2731, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2727 in
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
                                             let uu____2744 =
                                               let uu____2748 =
                                                 let uu____2749 =
                                                   let uu____2755 =
                                                     let uu____2756 =
                                                       let uu____2759 =
                                                         let uu____2760 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2760 in
                                                       (f_has_t, uu____2759) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2756 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2755) in
                                                 mkForall_fuel uu____2749 in
                                               (uu____2748,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2744 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2773 =
                                               let uu____2777 =
                                                 let uu____2778 =
                                                   let uu____2784 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2784) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2778 in
                                               (uu____2777, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2773 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2798 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2798);
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
                     let uu____2809 =
                       let uu____2813 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2813, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2809 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2822 =
                       let uu____2826 =
                         let uu____2827 =
                           let uu____2833 =
                             let uu____2834 =
                               let uu____2837 =
                                 let uu____2838 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2838 in
                               (f_has_t, uu____2837) in
                             FStar_SMTEncoding_Util.mkImp uu____2834 in
                           ([[f_has_t]], [fsym], uu____2833) in
                         mkForall_fuel uu____2827 in
                       (uu____2826, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2822 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2852 ->
           let uu____2857 =
             let uu____2860 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2860 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2865;
                 FStar_Syntax_Syntax.pos = uu____2866;
                 FStar_Syntax_Syntax.vars = uu____2867;_} ->
                 let uu____2874 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2874 with
                  | (b,f1) ->
                      let uu____2888 =
                        let uu____2889 = FStar_List.hd b in
                        Prims.fst uu____2889 in
                      (uu____2888, f1))
             | uu____2894 -> failwith "impossible" in
           (match uu____2857 with
            | (x,f) ->
                let uu____2901 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2901 with
                 | (base_t,decls) ->
                     let uu____2908 = gen_term_var env x in
                     (match uu____2908 with
                      | (x1,xtm,env') ->
                          let uu____2917 = encode_formula f env' in
                          (match uu____2917 with
                           | (refinement,decls') ->
                               let uu____2924 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2924 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2935 =
                                        let uu____2937 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2941 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2937
                                          uu____2941 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2935 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2957  ->
                                              match uu____2957 with
                                              | (y,uu____2961) ->
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
                                    let uu____2980 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2980 with
                                     | Some cache_entry ->
                                         let uu____2985 =
                                           let uu____2986 =
                                             let uu____2990 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____2990) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2986 in
                                         (uu____2985,
                                           (use_cache_entry cache_entry))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3002 =
                                             let uu____3003 =
                                               let uu____3004 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3004 in
                                             Prims.strcat module_name
                                               uu____3003 in
                                           varops.mk_unique uu____3002 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3013 =
                                             let uu____3017 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3017) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3013 in
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
                                           let uu____3027 =
                                             let uu____3031 =
                                               let uu____3032 =
                                                 let uu____3038 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3038) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3032 in
                                             (uu____3031,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3027 in
                                         let t_kinding =
                                           let uu____3048 =
                                             let uu____3052 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3052,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3048 in
                                         let t_interp =
                                           let uu____3062 =
                                             let uu____3066 =
                                               let uu____3067 =
                                                 let uu____3073 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3073) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3067 in
                                             let uu____3085 =
                                               let uu____3087 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3087 in
                                             (uu____3066, uu____3085,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3062 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3092 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3092);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3109 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3109 in
           let uu____3113 = encode_term_pred None k env ttm in
           (match uu____3113 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3121 =
                    let uu____3125 =
                      let uu____3126 =
                        let uu____3127 =
                          let uu____3128 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3128 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3127 in
                      varops.mk_unique uu____3126 in
                    (t_has_k, (Some "Uvar typing"), uu____3125) in
                  FStar_SMTEncoding_Util.mkAssume uu____3121 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3134 ->
           let uu____3144 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3144 with
            | (head1,args_e) ->
                let uu____3172 =
                  let uu____3180 =
                    let uu____3181 = FStar_Syntax_Subst.compress head1 in
                    uu____3181.FStar_Syntax_Syntax.n in
                  (uu____3180, args_e) in
                (match uu____3172 with
                 | (uu____3191,uu____3192) when head_redex env head1 ->
                     let uu____3203 = whnf env t in
                     encode_term uu____3203 env
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
                     let uu____3277 = encode_term v1 env in
                     (match uu____3277 with
                      | (v11,decls1) ->
                          let uu____3284 = encode_term v2 env in
                          (match uu____3284 with
                           | (v21,decls2) ->
                               let uu____3291 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3291,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3293) ->
                     let e0 =
                       let uu____3307 =
                         let uu____3310 =
                           let uu____3311 =
                             let uu____3321 =
                               let uu____3327 = FStar_List.hd args_e in
                               [uu____3327] in
                             (head1, uu____3321) in
                           FStar_Syntax_Syntax.Tm_app uu____3311 in
                         FStar_Syntax_Syntax.mk uu____3310 in
                       uu____3307 None head1.FStar_Syntax_Syntax.pos in
                     ((let uu____3360 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3360
                       then
                         let uu____3361 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Trying to normalize %s\n"
                           uu____3361
                       else ());
                      (let e01 =
                         FStar_TypeChecker_Normalize.normalize
                           [FStar_TypeChecker_Normalize.Beta;
                           FStar_TypeChecker_Normalize.Reify;
                           FStar_TypeChecker_Normalize.Eager_unfolding;
                           FStar_TypeChecker_Normalize.EraseUniverses;
                           FStar_TypeChecker_Normalize.AllowUnboundUniverses]
                           env.tcenv e0 in
                       (let uu____3365 =
                          FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug env.tcenv)
                            (FStar_Options.Other "SMTEncodingReify") in
                        if uu____3365
                        then
                          let uu____3366 =
                            FStar_Syntax_Print.term_to_string e01 in
                          FStar_Util.print1 "Result of normalization %s\n"
                            uu____3366
                        else ());
                       (let e02 =
                          let uu____3369 =
                            let uu____3370 =
                              let uu____3371 =
                                FStar_Syntax_Subst.compress e01 in
                              uu____3371.FStar_Syntax_Syntax.n in
                            match uu____3370 with
                            | FStar_Syntax_Syntax.Tm_app uu____3374 -> false
                            | uu____3384 -> true in
                          if uu____3369
                          then e01
                          else
                            (let uu____3386 =
                               FStar_Syntax_Util.head_and_args e01 in
                             match uu____3386 with
                             | (head2,args) ->
                                 let uu____3412 =
                                   let uu____3413 =
                                     let uu____3414 =
                                       FStar_Syntax_Subst.compress head2 in
                                     uu____3414.FStar_Syntax_Syntax.n in
                                   match uu____3413 with
                                   | FStar_Syntax_Syntax.Tm_constant
                                       (FStar_Const.Const_reify ) -> true
                                   | uu____3417 -> false in
                                 if uu____3412
                                 then
                                   (match args with
                                    | x::[] -> Prims.fst x
                                    | uu____3433 ->
                                        failwith
                                          "Impossible : Reify applied to multiple arguments after normalization.")
                                 else e01) in
                        let e =
                          match args_e with
                          | uu____3441::[] -> e02
                          | uu____3454 ->
                              let uu____3460 =
                                let uu____3463 =
                                  let uu____3464 =
                                    let uu____3474 = FStar_List.tl args_e in
                                    (e02, uu____3474) in
                                  FStar_Syntax_Syntax.Tm_app uu____3464 in
                                FStar_Syntax_Syntax.mk uu____3463 in
                              uu____3460 None t0.FStar_Syntax_Syntax.pos in
                        encode_term e env)))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3497),(arg,uu____3499)::[]) -> encode_term arg env
                 | uu____3517 ->
                     let uu____3525 = encode_args args_e env in
                     (match uu____3525 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3558 = encode_term head1 env in
                            match uu____3558 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3597 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3597 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3639  ->
                                                 fun uu____3640  ->
                                                   match (uu____3639,
                                                           uu____3640)
                                                   with
                                                   | ((bv,uu____3654),
                                                      (a,uu____3656)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3670 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3670
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3675 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3675 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3685 =
                                                   let uu____3689 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3694 =
                                                     let uu____3695 =
                                                       let uu____3696 =
                                                         let uu____3697 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3697 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3696 in
                                                     varops.mk_unique
                                                       uu____3695 in
                                                   (uu____3689,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3694) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3685 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3714 = lookup_free_var_sym env fv in
                            match uu____3714 with
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
                                let uu____3752 =
                                  let uu____3753 =
                                    let uu____3756 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3756 Prims.fst in
                                  FStar_All.pipe_right uu____3753 Prims.snd in
                                Some uu____3752
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3775,(FStar_Util.Inl t1,uu____3777),uu____3778)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3816,(FStar_Util.Inr c,uu____3818),uu____3819)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3857 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3877 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3877 in
                               let uu____3878 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3878 with
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
                                     | uu____3903 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3948 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3948 with
            | (bs1,body1,opening) ->
                let fallback uu____3963 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3968 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3968, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3979 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3979
                  | FStar_Util.Inr (eff,uu____3981) ->
                      let uu____3987 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3987 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body = reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4032 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___138_4033 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___138_4033.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___138_4033.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___138_4033.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___138_4033.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___138_4033.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___138_4033.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___138_4033.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___138_4033.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___138_4033.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___138_4033.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___138_4033.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___138_4033.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___138_4033.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___138_4033.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___138_4033.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___138_4033.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___138_4033.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___138_4033.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___138_4033.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___138_4033.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___138_4033.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___138_4033.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___138_4033.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4032 FStar_Syntax_Syntax.U_unknown in
                        let uu____4034 =
                          let uu____4035 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4035 in
                        FStar_Util.Inl uu____4034
                    | FStar_Util.Inr (eff_name,uu____4042) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4073 =
                        let uu____4074 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4074 in
                      FStar_All.pipe_right uu____4073
                        (fun _0_30  -> Some _0_30)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4086 =
                        let uu____4087 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4087 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4095 =
                          let uu____4096 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4096 in
                        FStar_All.pipe_right uu____4095
                          (fun _0_31  -> Some _0_31)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4100 =
                             let uu____4101 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4101 in
                           FStar_All.pipe_right uu____4100
                             (fun _0_32  -> Some _0_32))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4112 =
                         let uu____4113 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4113 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4112);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4128 =
                       (is_impure lc1) &&
                         (let uu____4129 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4129) in
                     if uu____4128
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4134 = encode_binders None bs1 env in
                        match uu____4134 with
                        | (vars,guards,envbody,decls,uu____4149) ->
                            let uu____4156 =
                              let uu____4164 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4164
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4156 with
                             | (lc2,body2) ->
                                 let uu____4189 = encode_term body2 envbody in
                                 (match uu____4189 with
                                  | (body3,decls') ->
                                      let uu____4196 =
                                        let uu____4201 = codomain_eff lc2 in
                                        match uu____4201 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4213 =
                                              encode_term tfun env in
                                            (match uu____4213 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4196 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4232 =
                                               let uu____4238 =
                                                 let uu____4239 =
                                                   let uu____4242 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4242, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4239 in
                                               ([], vars, uu____4238) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4232 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4250 =
                                                   let uu____4252 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4252 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4250 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4263 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4263 with
                                            | Some cache_entry ->
                                                let uu____4268 =
                                                  let uu____4269 =
                                                    let uu____4273 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4273) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4269 in
                                                (uu____4268,
                                                  (use_cache_entry
                                                     cache_entry))
                                            | None  ->
                                                let uu____4279 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4279 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4286 =
                                                         let uu____4287 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4287 =
                                                           cache_size in
                                                       if uu____4286
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
                                                         let uu____4298 =
                                                           let uu____4299 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4299 in
                                                         varops.mk_unique
                                                           uu____4298 in
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
                                                       let uu____4304 =
                                                         let uu____4308 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4308) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4304 in
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
                                                           let uu____4320 =
                                                             let uu____4321 =
                                                               let uu____4325
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4325,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4321 in
                                                           [uu____4320] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4333 =
                                                         let uu____4337 =
                                                           let uu____4338 =
                                                             let uu____4344 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4344) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4338 in
                                                         (uu____4337,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4333 in
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
                                                     ((let uu____4354 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4354);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4356,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4357;
                          FStar_Syntax_Syntax.lbunivs = uu____4358;
                          FStar_Syntax_Syntax.lbtyp = uu____4359;
                          FStar_Syntax_Syntax.lbeff = uu____4360;
                          FStar_Syntax_Syntax.lbdef = uu____4361;_}::uu____4362),uu____4363)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4381;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4383;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4399 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4412 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4412, [decl_e])))
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
              let uu____4454 = encode_term e1 env in
              match uu____4454 with
              | (ee1,decls1) ->
                  let uu____4461 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4461 with
                   | (xs,e21) ->
                       let uu____4475 = FStar_List.hd xs in
                       (match uu____4475 with
                        | (x1,uu____4483) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4485 = encode_body e21 env' in
                            (match uu____4485 with
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
            let uu____4507 =
              let uu____4511 =
                let uu____4512 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4512 in
              gen_term_var env uu____4511 in
            match uu____4507 with
            | (scrsym,scr',env1) ->
                let uu____4526 = encode_term e env1 in
                (match uu____4526 with
                 | (scr,decls) ->
                     let uu____4533 =
                       let encode_branch b uu____4549 =
                         match uu____4549 with
                         | (else_case,decls1) ->
                             let uu____4560 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4560 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4590  ->
                                       fun uu____4591  ->
                                         match (uu____4590, uu____4591) with
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
                                                       fun uu____4628  ->
                                                         match uu____4628
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4633 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4648 =
                                                     encode_term w1 env2 in
                                                   (match uu____4648 with
                                                    | (w2,decls21) ->
                                                        let uu____4656 =
                                                          let uu____4657 =
                                                            let uu____4660 =
                                                              let uu____4661
                                                                =
                                                                let uu____4664
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4664) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4661 in
                                                            (guard,
                                                              uu____4660) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4657 in
                                                        (uu____4656, decls21)) in
                                             (match uu____4633 with
                                              | (guard1,decls21) ->
                                                  let uu____4672 =
                                                    encode_br br env2 in
                                                  (match uu____4672 with
                                                   | (br1,decls3) ->
                                                       let uu____4680 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4680,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4533 with
                      | (match_tm,decls1) ->
                          let uu____4692 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4692, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4723 -> let uu____4724 = encode_one_pat env pat in [uu____4724]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4736 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4736
       then
         let uu____4737 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4737
       else ());
      (let uu____4739 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4739 with
       | (vars,pat_term) ->
           let uu____4749 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4772  ->
                     fun v1  ->
                       match uu____4772 with
                       | (env1,vars1) ->
                           let uu____4800 = gen_term_var env1 v1 in
                           (match uu____4800 with
                            | (xx,uu____4812,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4749 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4859 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4867 =
                        let uu____4870 = encode_const c in
                        (scrutinee, uu____4870) in
                      FStar_SMTEncoding_Util.mkEq uu____4867
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4889 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4889 with
                        | (uu____4893,uu____4894::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4896 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4917  ->
                                  match uu____4917 with
                                  | (arg,uu____4923) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4933 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4933)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4952 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4967 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4982 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5004  ->
                                  match uu____5004 with
                                  | (arg,uu____5013) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5023 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5023)) in
                      FStar_All.pipe_right uu____4982 FStar_List.flatten in
                let pat_term1 uu____5039 = encode_term pat_term env1 in
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
      let uu____5046 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5061  ->
                fun uu____5062  ->
                  match (uu____5061, uu____5062) with
                  | ((tms,decls),(t,uu____5082)) ->
                      let uu____5093 = encode_term t env in
                      (match uu____5093 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5046 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_SMTEncoding_Term.term Prims.option ->
    FStar_Syntax_Syntax.term Prims.option ->
      FStar_Syntax_Syntax.typ ->
        env_t ->
          (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun induction_on  ->
    fun new_pats  ->
      fun t  ->
        fun env  ->
          let list_elements1 e =
            let uu____5131 = FStar_Syntax_Util.list_elements e in
            match uu____5131 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____5149 =
              let uu____5159 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____5159 FStar_Syntax_Util.head_and_args in
            match uu____5149 with
            | (head1,args) ->
                let uu____5190 =
                  let uu____5198 =
                    let uu____5199 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5199.FStar_Syntax_Syntax.n in
                  (uu____5198, args) in
                (match uu____5190 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5213,uu____5214)::(e,uu____5216)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5247)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5268 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5301 =
                let uu____5311 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5311
                  FStar_Syntax_Util.head_and_args in
              match uu____5301 with
              | (head1,args) ->
                  let uu____5340 =
                    let uu____5348 =
                      let uu____5349 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5349.FStar_Syntax_Syntax.n in
                    (uu____5348, args) in
                  (match uu____5340 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5362)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5382 -> None) in
            match elts with
            | t1::[] ->
                let uu____5400 = smt_pat_or t1 in
                (match uu____5400 with
                 | Some e ->
                     let uu____5416 = list_elements1 e in
                     FStar_All.pipe_right uu____5416
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5433 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5433
                               (FStar_List.map one_pat)))
                 | uu____5447 ->
                     let uu____5451 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5451])
            | uu____5482 ->
                let uu____5484 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5484] in
          let uu____5515 =
            let uu____5531 =
              let uu____5532 = FStar_Syntax_Subst.compress t in
              uu____5532.FStar_Syntax_Syntax.n in
            match uu____5531 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5562 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5562 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5597;
                            FStar_Syntax_Syntax.effect_name = uu____5598;
                            FStar_Syntax_Syntax.result_typ = uu____5599;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5601)::(post,uu____5603)::(pats,uu____5605)::[];
                            FStar_Syntax_Syntax.flags = uu____5606;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5640 = lemma_pats pats' in
                          (binders1, pre, post, uu____5640)
                      | uu____5659 -> failwith "impos"))
            | uu____5675 -> failwith "Impos" in
          match uu____5515 with
          | (binders,pre,post,patterns) ->
              let uu____5719 = encode_binders None binders env in
              (match uu____5719 with
               | (vars,guards,env1,decls,uu____5734) ->
                   let uu____5741 =
                     let uu____5748 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5779 =
                                 let uu____5784 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5800  ->
                                           match uu____5800 with
                                           | (t1,uu____5807) ->
                                               encode_term t1
                                                 (let uu___139_5810 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___139_5810.bindings);
                                                    depth =
                                                      (uu___139_5810.depth);
                                                    tcenv =
                                                      (uu___139_5810.tcenv);
                                                    warn =
                                                      (uu___139_5810.warn);
                                                    cache =
                                                      (uu___139_5810.cache);
                                                    nolabels =
                                                      (uu___139_5810.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___139_5810.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___139_5810.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5784
                                   FStar_List.unzip in
                               match uu____5779 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5748 FStar_List.unzip in
                   (match uu____5741 with
                    | (pats,decls') ->
                        let decls'1 = FStar_List.flatten decls' in
                        let pats1 =
                          match induction_on with
                          | None  -> pats
                          | Some e ->
                              (match vars with
                               | [] -> pats
                               | l::[] ->
                                   FStar_All.pipe_right pats
                                     (FStar_List.map
                                        (fun p  ->
                                           let uu____5874 =
                                             let uu____5875 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5875 e in
                                           uu____5874 :: p))
                               | uu____5876 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5905 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5905 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5913 =
                                           let uu____5914 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5914 tl1 in
                                         aux uu____5913 vars2
                                     | uu____5915 -> pats in
                                   let uu____5919 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5919 vars) in
                        let env2 =
                          let uu___140_5921 = env1 in
                          {
                            bindings = (uu___140_5921.bindings);
                            depth = (uu___140_5921.depth);
                            tcenv = (uu___140_5921.tcenv);
                            warn = (uu___140_5921.warn);
                            cache = (uu___140_5921.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___140_5921.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___140_5921.encode_non_total_function_typ);
                            current_module_name =
                              (uu___140_5921.current_module_name)
                          } in
                        let uu____5922 =
                          let uu____5925 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5925 env2 in
                        (match uu____5922 with
                         | (pre1,decls'') ->
                             let uu____5930 =
                               let uu____5933 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5933 env2 in
                             (match uu____5930 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5940 =
                                    let uu____5941 =
                                      let uu____5947 =
                                        let uu____5948 =
                                          let uu____5951 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5951, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5948 in
                                      (pats1, vars, uu____5947) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5941 in
                                  (uu____5940, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5964 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5964
        then
          let uu____5965 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5966 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5965 uu____5966
        else () in
      let enc f r l =
        let uu____5993 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6006 = encode_term (Prims.fst x) env in
                 match uu____6006 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5993 with
        | (decls,args) ->
            let uu____6023 =
              let uu___141_6024 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___141_6024.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___141_6024.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6023, decls) in
      let const_op f r uu____6043 = let uu____6046 = f r in (uu____6046, []) in
      let un_op f l =
        let uu____6062 = FStar_List.hd l in FStar_All.pipe_left f uu____6062 in
      let bin_op f uu___113_6075 =
        match uu___113_6075 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6083 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6110 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6119  ->
                 match uu____6119 with
                 | (t,uu____6127) ->
                     let uu____6128 = encode_formula t env in
                     (match uu____6128 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6110 with
        | (decls,phis) ->
            let uu____6145 =
              let uu___142_6146 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___142_6146.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___142_6146.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6145, decls) in
      let eq_op r uu___114_6162 =
        match uu___114_6162 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6222 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6222 r [e1; e2]
        | l ->
            let uu____6242 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6242 r l in
      let mk_imp1 r uu___115_6261 =
        match uu___115_6261 with
        | (lhs,uu____6265)::(rhs,uu____6267)::[] ->
            let uu____6288 = encode_formula rhs env in
            (match uu____6288 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6297) ->
                      (l1, decls1)
                  | uu____6300 ->
                      let uu____6301 = encode_formula lhs env in
                      (match uu____6301 with
                       | (l2,decls2) ->
                           let uu____6308 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6308, (FStar_List.append decls1 decls2)))))
        | uu____6310 -> failwith "impossible" in
      let mk_ite r uu___116_6325 =
        match uu___116_6325 with
        | (guard,uu____6329)::(_then,uu____6331)::(_else,uu____6333)::[] ->
            let uu____6362 = encode_formula guard env in
            (match uu____6362 with
             | (g,decls1) ->
                 let uu____6369 = encode_formula _then env in
                 (match uu____6369 with
                  | (t,decls2) ->
                      let uu____6376 = encode_formula _else env in
                      (match uu____6376 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6385 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6404 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6404 in
      let connectives =
        let uu____6416 =
          let uu____6425 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6425) in
        let uu____6438 =
          let uu____6448 =
            let uu____6457 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6457) in
          let uu____6470 =
            let uu____6480 =
              let uu____6490 =
                let uu____6499 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6499) in
              let uu____6512 =
                let uu____6522 =
                  let uu____6532 =
                    let uu____6541 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6541) in
                  [uu____6532;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6522 in
              uu____6490 :: uu____6512 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6480 in
          uu____6448 :: uu____6470 in
        uu____6416 :: uu____6438 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6703 = encode_formula phi' env in
            (match uu____6703 with
             | (phi2,decls) ->
                 let uu____6710 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6710, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6711 ->
            let uu____6716 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6716 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6745 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6745 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6753;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6755;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6771 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6771 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6803::(x,uu____6805)::(t,uu____6807)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6841 = encode_term x env in
                 (match uu____6841 with
                  | (x1,decls) ->
                      let uu____6848 = encode_term t env in
                      (match uu____6848 with
                       | (t1,decls') ->
                           let uu____6855 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6855, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6859)::(msg,uu____6861)::(phi2,uu____6863)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6897 =
                   let uu____6900 =
                     let uu____6901 = FStar_Syntax_Subst.compress r in
                     uu____6901.FStar_Syntax_Syntax.n in
                   let uu____6904 =
                     let uu____6905 = FStar_Syntax_Subst.compress msg in
                     uu____6905.FStar_Syntax_Syntax.n in
                   (uu____6900, uu____6904) in
                 (match uu____6897 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6912))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6928 -> fallback phi2)
             | uu____6931 when head_redex env head2 ->
                 let uu____6939 = whnf env phi1 in
                 encode_formula uu____6939 env
             | uu____6940 ->
                 let uu____6948 = encode_term phi1 env in
                 (match uu____6948 with
                  | (tt,decls) ->
                      let uu____6955 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___143_6956 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___143_6956.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___143_6956.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6955, decls)))
        | uu____6959 ->
            let uu____6960 = encode_term phi1 env in
            (match uu____6960 with
             | (tt,decls) ->
                 let uu____6967 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___144_6968 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___144_6968.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___144_6968.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6967, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6995 = encode_binders None bs env1 in
        match uu____6995 with
        | (vars,guards,env2,decls,uu____7017) ->
            let uu____7024 =
              let uu____7031 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7054 =
                          let uu____7059 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7073  ->
                                    match uu____7073 with
                                    | (t,uu____7079) ->
                                        encode_term t
                                          (let uu___145_7080 = env2 in
                                           {
                                             bindings =
                                               (uu___145_7080.bindings);
                                             depth = (uu___145_7080.depth);
                                             tcenv = (uu___145_7080.tcenv);
                                             warn = (uu___145_7080.warn);
                                             cache = (uu___145_7080.cache);
                                             nolabels =
                                               (uu___145_7080.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___145_7080.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___145_7080.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7059 FStar_List.unzip in
                        match uu____7054 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7031 FStar_List.unzip in
            (match uu____7024 with
             | (pats,decls') ->
                 let uu____7132 = encode_formula body env2 in
                 (match uu____7132 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7151;
                             FStar_SMTEncoding_Term.rng = uu____7152;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7160 -> guards in
                      let uu____7163 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7163, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7197  ->
                   match uu____7197 with
                   | (x,uu____7201) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7207 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7213 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7213) uu____7207 tl1 in
             let uu____7215 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7227  ->
                       match uu____7227 with
                       | (b,uu____7231) ->
                           let uu____7232 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7232)) in
             (match uu____7215 with
              | None  -> ()
              | Some (x,uu____7236) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7246 =
                    let uu____7247 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7247 in
                  FStar_Errors.warn pos uu____7246) in
       let uu____7248 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7248 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7254 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7290  ->
                     match uu____7290 with
                     | (l,uu____7300) -> FStar_Ident.lid_equals op l)) in
           (match uu____7254 with
            | None  -> fallback phi1
            | Some (uu____7323,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7352 = encode_q_body env vars pats body in
             match uu____7352 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7378 =
                     let uu____7384 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7384) in
                   FStar_SMTEncoding_Term.mkForall uu____7378
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7396 = encode_q_body env vars pats body in
             match uu____7396 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7421 =
                   let uu____7422 =
                     let uu____7428 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7428) in
                   FStar_SMTEncoding_Term.mkExists uu____7422
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7421, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7477 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7477 with
  | (asym,a) ->
      let uu____7482 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7482 with
       | (xsym,x) ->
           let uu____7487 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7487 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7517 =
                      let uu____7523 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7523, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7517 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7538 =
                      let uu____7542 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7542) in
                    FStar_SMTEncoding_Util.mkApp uu____7538 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7550 =
                    let uu____7552 =
                      let uu____7554 =
                        let uu____7556 =
                          let uu____7557 =
                            let uu____7561 =
                              let uu____7562 =
                                let uu____7568 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7568) in
                              FStar_SMTEncoding_Util.mkForall uu____7562 in
                            (uu____7561, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7557 in
                        let uu____7577 =
                          let uu____7579 =
                            let uu____7580 =
                              let uu____7584 =
                                let uu____7585 =
                                  let uu____7591 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7591) in
                                FStar_SMTEncoding_Util.mkForall uu____7585 in
                              (uu____7584,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7580 in
                          [uu____7579] in
                        uu____7556 :: uu____7577 in
                      xtok_decl :: uu____7554 in
                    xname_decl :: uu____7552 in
                  (xtok1, uu____7550) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7640 =
                    let uu____7648 =
                      let uu____7654 =
                        let uu____7655 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7655 in
                      quant axy uu____7654 in
                    (FStar_Syntax_Const.op_Eq, uu____7648) in
                  let uu____7661 =
                    let uu____7670 =
                      let uu____7678 =
                        let uu____7684 =
                          let uu____7685 =
                            let uu____7686 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7686 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7685 in
                        quant axy uu____7684 in
                      (FStar_Syntax_Const.op_notEq, uu____7678) in
                    let uu____7692 =
                      let uu____7701 =
                        let uu____7709 =
                          let uu____7715 =
                            let uu____7716 =
                              let uu____7717 =
                                let uu____7720 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7721 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7720, uu____7721) in
                              FStar_SMTEncoding_Util.mkLT uu____7717 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7716 in
                          quant xy uu____7715 in
                        (FStar_Syntax_Const.op_LT, uu____7709) in
                      let uu____7727 =
                        let uu____7736 =
                          let uu____7744 =
                            let uu____7750 =
                              let uu____7751 =
                                let uu____7752 =
                                  let uu____7755 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7756 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7755, uu____7756) in
                                FStar_SMTEncoding_Util.mkLTE uu____7752 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7751 in
                            quant xy uu____7750 in
                          (FStar_Syntax_Const.op_LTE, uu____7744) in
                        let uu____7762 =
                          let uu____7771 =
                            let uu____7779 =
                              let uu____7785 =
                                let uu____7786 =
                                  let uu____7787 =
                                    let uu____7790 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7791 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7790, uu____7791) in
                                  FStar_SMTEncoding_Util.mkGT uu____7787 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7786 in
                              quant xy uu____7785 in
                            (FStar_Syntax_Const.op_GT, uu____7779) in
                          let uu____7797 =
                            let uu____7806 =
                              let uu____7814 =
                                let uu____7820 =
                                  let uu____7821 =
                                    let uu____7822 =
                                      let uu____7825 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7826 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7825, uu____7826) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7822 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7821 in
                                quant xy uu____7820 in
                              (FStar_Syntax_Const.op_GTE, uu____7814) in
                            let uu____7832 =
                              let uu____7841 =
                                let uu____7849 =
                                  let uu____7855 =
                                    let uu____7856 =
                                      let uu____7857 =
                                        let uu____7860 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7861 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7860, uu____7861) in
                                      FStar_SMTEncoding_Util.mkSub uu____7857 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7856 in
                                  quant xy uu____7855 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7849) in
                              let uu____7867 =
                                let uu____7876 =
                                  let uu____7884 =
                                    let uu____7890 =
                                      let uu____7891 =
                                        let uu____7892 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7892 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7891 in
                                    quant qx uu____7890 in
                                  (FStar_Syntax_Const.op_Minus, uu____7884) in
                                let uu____7898 =
                                  let uu____7907 =
                                    let uu____7915 =
                                      let uu____7921 =
                                        let uu____7922 =
                                          let uu____7923 =
                                            let uu____7926 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7927 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7926, uu____7927) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7923 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7922 in
                                      quant xy uu____7921 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7915) in
                                  let uu____7933 =
                                    let uu____7942 =
                                      let uu____7950 =
                                        let uu____7956 =
                                          let uu____7957 =
                                            let uu____7958 =
                                              let uu____7961 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7962 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7961, uu____7962) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7958 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7957 in
                                        quant xy uu____7956 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7950) in
                                    let uu____7968 =
                                      let uu____7977 =
                                        let uu____7985 =
                                          let uu____7991 =
                                            let uu____7992 =
                                              let uu____7993 =
                                                let uu____7996 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7997 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7996, uu____7997) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7993 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7992 in
                                          quant xy uu____7991 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7985) in
                                      let uu____8003 =
                                        let uu____8012 =
                                          let uu____8020 =
                                            let uu____8026 =
                                              let uu____8027 =
                                                let uu____8028 =
                                                  let uu____8031 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8032 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8031, uu____8032) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8028 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8027 in
                                            quant xy uu____8026 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8020) in
                                        let uu____8038 =
                                          let uu____8047 =
                                            let uu____8055 =
                                              let uu____8061 =
                                                let uu____8062 =
                                                  let uu____8063 =
                                                    let uu____8066 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8067 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8066, uu____8067) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8063 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8062 in
                                              quant xy uu____8061 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8055) in
                                          let uu____8073 =
                                            let uu____8082 =
                                              let uu____8090 =
                                                let uu____8096 =
                                                  let uu____8097 =
                                                    let uu____8098 =
                                                      let uu____8101 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8102 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8101,
                                                        uu____8102) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8098 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8097 in
                                                quant xy uu____8096 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8090) in
                                            let uu____8108 =
                                              let uu____8117 =
                                                let uu____8125 =
                                                  let uu____8131 =
                                                    let uu____8132 =
                                                      let uu____8133 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8133 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8132 in
                                                  quant qx uu____8131 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8125) in
                                              [uu____8117] in
                                            uu____8082 :: uu____8108 in
                                          uu____8047 :: uu____8073 in
                                        uu____8012 :: uu____8038 in
                                      uu____7977 :: uu____8003 in
                                    uu____7942 :: uu____7968 in
                                  uu____7907 :: uu____7933 in
                                uu____7876 :: uu____7898 in
                              uu____7841 :: uu____7867 in
                            uu____7806 :: uu____7832 in
                          uu____7771 :: uu____7797 in
                        uu____7736 :: uu____7762 in
                      uu____7701 :: uu____7727 in
                    uu____7670 :: uu____7692 in
                  uu____7640 :: uu____7661 in
                let mk1 l v1 =
                  let uu____8261 =
                    let uu____8266 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8298  ->
                              match uu____8298 with
                              | (l',uu____8307) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8266
                      (FStar_Option.map
                         (fun uu____8340  ->
                            match uu____8340 with | (uu____8351,b) -> b v1)) in
                  FStar_All.pipe_right uu____8261 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8392  ->
                          match uu____8392 with
                          | (l',uu____8401) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8427 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8427 with
        | (xxsym,xx) ->
            let uu____8432 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8432 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8440 =
                   let uu____8444 =
                     let uu____8445 =
                       let uu____8451 =
                         let uu____8452 =
                           let uu____8455 =
                             let uu____8456 =
                               let uu____8459 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8459) in
                             FStar_SMTEncoding_Util.mkEq uu____8456 in
                           (xx_has_type, uu____8455) in
                         FStar_SMTEncoding_Util.mkImp uu____8452 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8451) in
                     FStar_SMTEncoding_Util.mkForall uu____8445 in
                   let uu____8472 =
                     let uu____8473 =
                       let uu____8474 =
                         let uu____8475 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8475 in
                       Prims.strcat module_name uu____8474 in
                     varops.mk_unique uu____8473 in
                   (uu____8444, (Some "pretyping"), uu____8472) in
                 FStar_SMTEncoding_Util.mkAssume uu____8440)
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
    let uu____8505 =
      let uu____8506 =
        let uu____8510 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8510, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8506 in
    let uu____8512 =
      let uu____8514 =
        let uu____8515 =
          let uu____8519 =
            let uu____8520 =
              let uu____8526 =
                let uu____8527 =
                  let uu____8530 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8530) in
                FStar_SMTEncoding_Util.mkImp uu____8527 in
              ([[typing_pred]], [xx], uu____8526) in
            mkForall_fuel uu____8520 in
          (uu____8519, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8515 in
      [uu____8514] in
    uu____8505 :: uu____8512 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8558 =
      let uu____8559 =
        let uu____8563 =
          let uu____8564 =
            let uu____8570 =
              let uu____8573 =
                let uu____8575 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8575] in
              [uu____8573] in
            let uu____8578 =
              let uu____8579 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8579 tt in
            (uu____8570, [bb], uu____8578) in
          FStar_SMTEncoding_Util.mkForall uu____8564 in
        (uu____8563, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8559 in
    let uu____8590 =
      let uu____8592 =
        let uu____8593 =
          let uu____8597 =
            let uu____8598 =
              let uu____8604 =
                let uu____8605 =
                  let uu____8608 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8608) in
                FStar_SMTEncoding_Util.mkImp uu____8605 in
              ([[typing_pred]], [xx], uu____8604) in
            mkForall_fuel uu____8598 in
          (uu____8597, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8593 in
      [uu____8592] in
    uu____8558 :: uu____8590 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8642 =
        let uu____8643 =
          let uu____8647 =
            let uu____8649 =
              let uu____8651 =
                let uu____8653 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8654 =
                  let uu____8656 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8656] in
                uu____8653 :: uu____8654 in
              tt :: uu____8651 in
            tt :: uu____8649 in
          ("Prims.Precedes", uu____8647) in
        FStar_SMTEncoding_Util.mkApp uu____8643 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8642 in
    let precedes_y_x =
      let uu____8659 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8659 in
    let uu____8661 =
      let uu____8662 =
        let uu____8666 =
          let uu____8667 =
            let uu____8673 =
              let uu____8676 =
                let uu____8678 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8678] in
              [uu____8676] in
            let uu____8681 =
              let uu____8682 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8682 tt in
            (uu____8673, [bb], uu____8681) in
          FStar_SMTEncoding_Util.mkForall uu____8667 in
        (uu____8666, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8662 in
    let uu____8693 =
      let uu____8695 =
        let uu____8696 =
          let uu____8700 =
            let uu____8701 =
              let uu____8707 =
                let uu____8708 =
                  let uu____8711 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8711) in
                FStar_SMTEncoding_Util.mkImp uu____8708 in
              ([[typing_pred]], [xx], uu____8707) in
            mkForall_fuel uu____8701 in
          (uu____8700, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8696 in
      let uu____8724 =
        let uu____8726 =
          let uu____8727 =
            let uu____8731 =
              let uu____8732 =
                let uu____8738 =
                  let uu____8739 =
                    let uu____8742 =
                      let uu____8743 =
                        let uu____8745 =
                          let uu____8747 =
                            let uu____8749 =
                              let uu____8750 =
                                let uu____8753 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8754 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8753, uu____8754) in
                              FStar_SMTEncoding_Util.mkGT uu____8750 in
                            let uu____8755 =
                              let uu____8757 =
                                let uu____8758 =
                                  let uu____8761 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8762 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8761, uu____8762) in
                                FStar_SMTEncoding_Util.mkGTE uu____8758 in
                              let uu____8763 =
                                let uu____8765 =
                                  let uu____8766 =
                                    let uu____8769 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8770 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8769, uu____8770) in
                                  FStar_SMTEncoding_Util.mkLT uu____8766 in
                                [uu____8765] in
                              uu____8757 :: uu____8763 in
                            uu____8749 :: uu____8755 in
                          typing_pred_y :: uu____8747 in
                        typing_pred :: uu____8745 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8743 in
                    (uu____8742, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8739 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8738) in
              mkForall_fuel uu____8732 in
            (uu____8731, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8727 in
        [uu____8726] in
      uu____8695 :: uu____8724 in
    uu____8661 :: uu____8693 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8800 =
      let uu____8801 =
        let uu____8805 =
          let uu____8806 =
            let uu____8812 =
              let uu____8815 =
                let uu____8817 = FStar_SMTEncoding_Term.boxString b in
                [uu____8817] in
              [uu____8815] in
            let uu____8820 =
              let uu____8821 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8821 tt in
            (uu____8812, [bb], uu____8820) in
          FStar_SMTEncoding_Util.mkForall uu____8806 in
        (uu____8805, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8801 in
    let uu____8832 =
      let uu____8834 =
        let uu____8835 =
          let uu____8839 =
            let uu____8840 =
              let uu____8846 =
                let uu____8847 =
                  let uu____8850 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8850) in
                FStar_SMTEncoding_Util.mkImp uu____8847 in
              ([[typing_pred]], [xx], uu____8846) in
            mkForall_fuel uu____8840 in
          (uu____8839, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8835 in
      [uu____8834] in
    uu____8800 :: uu____8832 in
  let mk_ref1 env reft_name uu____8872 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8883 =
        let uu____8887 =
          let uu____8889 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8889] in
        (reft_name, uu____8887) in
      FStar_SMTEncoding_Util.mkApp uu____8883 in
    let refb =
      let uu____8892 =
        let uu____8896 =
          let uu____8898 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8898] in
        (reft_name, uu____8896) in
      FStar_SMTEncoding_Util.mkApp uu____8892 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8902 =
      let uu____8903 =
        let uu____8907 =
          let uu____8908 =
            let uu____8914 =
              let uu____8915 =
                let uu____8918 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8918) in
              FStar_SMTEncoding_Util.mkImp uu____8915 in
            ([[typing_pred]], [xx; aa], uu____8914) in
          mkForall_fuel uu____8908 in
        (uu____8907, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8903 in
    [uu____8902] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8958 =
      let uu____8959 =
        let uu____8963 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8963, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8959 in
    [uu____8958] in
  let mk_and_interp env conj uu____8974 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8991 =
      let uu____8992 =
        let uu____8996 =
          let uu____8997 =
            let uu____9003 =
              let uu____9004 =
                let uu____9007 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9007, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9004 in
            ([[l_and_a_b]], [aa; bb], uu____9003) in
          FStar_SMTEncoding_Util.mkForall uu____8997 in
        (uu____8996, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8992 in
    [uu____8991] in
  let mk_or_interp env disj uu____9031 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9048 =
      let uu____9049 =
        let uu____9053 =
          let uu____9054 =
            let uu____9060 =
              let uu____9061 =
                let uu____9064 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9064, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9061 in
            ([[l_or_a_b]], [aa; bb], uu____9060) in
          FStar_SMTEncoding_Util.mkForall uu____9054 in
        (uu____9053, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9049 in
    [uu____9048] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9105 =
      let uu____9106 =
        let uu____9110 =
          let uu____9111 =
            let uu____9117 =
              let uu____9118 =
                let uu____9121 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9121, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9118 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9117) in
          FStar_SMTEncoding_Util.mkForall uu____9111 in
        (uu____9110, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9106 in
    [uu____9105] in
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
    let uu____9168 =
      let uu____9169 =
        let uu____9173 =
          let uu____9174 =
            let uu____9180 =
              let uu____9181 =
                let uu____9184 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9184, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9181 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9180) in
          FStar_SMTEncoding_Util.mkForall uu____9174 in
        (uu____9173, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9169 in
    [uu____9168] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9229 =
      let uu____9230 =
        let uu____9234 =
          let uu____9235 =
            let uu____9241 =
              let uu____9242 =
                let uu____9245 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9245, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9242 in
            ([[l_imp_a_b]], [aa; bb], uu____9241) in
          FStar_SMTEncoding_Util.mkForall uu____9235 in
        (uu____9234, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9230 in
    [uu____9229] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9286 =
      let uu____9287 =
        let uu____9291 =
          let uu____9292 =
            let uu____9298 =
              let uu____9299 =
                let uu____9302 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9302, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9299 in
            ([[l_iff_a_b]], [aa; bb], uu____9298) in
          FStar_SMTEncoding_Util.mkForall uu____9292 in
        (uu____9291, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9287 in
    [uu____9286] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9336 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9336 in
    let uu____9338 =
      let uu____9339 =
        let uu____9343 =
          let uu____9344 =
            let uu____9350 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9350) in
          FStar_SMTEncoding_Util.mkForall uu____9344 in
        (uu____9343, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9339 in
    [uu____9338] in
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
      let uu____9390 =
        let uu____9394 =
          let uu____9396 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9396] in
        ("Valid", uu____9394) in
      FStar_SMTEncoding_Util.mkApp uu____9390 in
    let uu____9398 =
      let uu____9399 =
        let uu____9403 =
          let uu____9404 =
            let uu____9410 =
              let uu____9411 =
                let uu____9414 =
                  let uu____9415 =
                    let uu____9421 =
                      let uu____9424 =
                        let uu____9426 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9426] in
                      [uu____9424] in
                    let uu____9429 =
                      let uu____9430 =
                        let uu____9433 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9433, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9430 in
                    (uu____9421, [xx1], uu____9429) in
                  FStar_SMTEncoding_Util.mkForall uu____9415 in
                (uu____9414, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9411 in
            ([[l_forall_a_b]], [aa; bb], uu____9410) in
          FStar_SMTEncoding_Util.mkForall uu____9404 in
        (uu____9403, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9399 in
    [uu____9398] in
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
      let uu____9484 =
        let uu____9488 =
          let uu____9490 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9490] in
        ("Valid", uu____9488) in
      FStar_SMTEncoding_Util.mkApp uu____9484 in
    let uu____9492 =
      let uu____9493 =
        let uu____9497 =
          let uu____9498 =
            let uu____9504 =
              let uu____9505 =
                let uu____9508 =
                  let uu____9509 =
                    let uu____9515 =
                      let uu____9518 =
                        let uu____9520 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9520] in
                      [uu____9518] in
                    let uu____9523 =
                      let uu____9524 =
                        let uu____9527 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9527, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9524 in
                    (uu____9515, [xx1], uu____9523) in
                  FStar_SMTEncoding_Util.mkExists uu____9509 in
                (uu____9508, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9505 in
            ([[l_exists_a_b]], [aa; bb], uu____9504) in
          FStar_SMTEncoding_Util.mkForall uu____9498 in
        (uu____9497, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9493 in
    [uu____9492] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9563 =
      let uu____9564 =
        let uu____9568 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9569 = varops.mk_unique "typing_range_const" in
        (uu____9568, (Some "Range_const typing"), uu____9569) in
      FStar_SMTEncoding_Util.mkAssume uu____9564 in
    [uu____9563] in
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
          let uu____9831 =
            FStar_Util.find_opt
              (fun uu____9849  ->
                 match uu____9849 with
                 | (l,uu____9859) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9831 with
          | None  -> []
          | Some (uu____9881,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9918 = encode_function_type_as_formula None None t env in
        match uu____9918 with
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
            let uu____9950 =
              (let uu____9951 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9951) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9950
            then
              let uu____9955 = new_term_constant_and_tok_from_lid env lid in
              match uu____9955 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9967 =
                      let uu____9968 = FStar_Syntax_Subst.compress t_norm in
                      uu____9968.FStar_Syntax_Syntax.n in
                    match uu____9967 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9973) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9990  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9993 -> [] in
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
              (let uu____10002 = prims.is lid in
               if uu____10002
               then
                 let vname = varops.new_fvar lid in
                 let uu____10007 = prims.mk lid vname in
                 match uu____10007 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10022 =
                    let uu____10028 = curried_arrow_formals_comp t_norm in
                    match uu____10028 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10039 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10039
                          then
                            let uu____10040 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___146_10041 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___146_10041.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___146_10041.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___146_10041.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___146_10041.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___146_10041.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___146_10041.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___146_10041.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___146_10041.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___146_10041.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___146_10041.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___146_10041.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___146_10041.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___146_10041.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___146_10041.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___146_10041.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___146_10041.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___146_10041.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___146_10041.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___146_10041.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___146_10041.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___146_10041.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___146_10041.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___146_10041.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10040
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10048 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10048)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10022 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10075 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10075 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10088 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___117_10112  ->
                                     match uu___117_10112 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10115 =
                                           FStar_Util.prefix vars in
                                         (match uu____10115 with
                                          | (uu____10126,(xxsym,uu____10128))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10138 =
                                                let uu____10139 =
                                                  let uu____10143 =
                                                    let uu____10144 =
                                                      let uu____10150 =
                                                        let uu____10151 =
                                                          let uu____10154 =
                                                            let uu____10155 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10155 in
                                                          (vapp, uu____10154) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10151 in
                                                      ([[vapp]], vars,
                                                        uu____10150) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10144 in
                                                  (uu____10143,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10139 in
                                              [uu____10138])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10166 =
                                           FStar_Util.prefix vars in
                                         (match uu____10166 with
                                          | (uu____10177,(xxsym,uu____10179))
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
                                              let uu____10193 =
                                                let uu____10194 =
                                                  let uu____10198 =
                                                    let uu____10199 =
                                                      let uu____10205 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10205) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10199 in
                                                  (uu____10198,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10194 in
                                              [uu____10193])
                                     | uu____10214 -> [])) in
                           let uu____10215 = encode_binders None formals env1 in
                           (match uu____10215 with
                            | (vars,guards,env',decls1,uu____10231) ->
                                let uu____10238 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10243 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10243, decls1)
                                  | Some p ->
                                      let uu____10245 = encode_formula p env' in
                                      (match uu____10245 with
                                       | (g,ds) ->
                                           let uu____10252 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10252,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10238 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10261 =
                                         let uu____10265 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10265) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10261 in
                                     let uu____10270 =
                                       let vname_decl =
                                         let uu____10275 =
                                           let uu____10281 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10286  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10281,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10275 in
                                       let uu____10291 =
                                         let env2 =
                                           let uu___147_10295 = env1 in
                                           {
                                             bindings =
                                               (uu___147_10295.bindings);
                                             depth = (uu___147_10295.depth);
                                             tcenv = (uu___147_10295.tcenv);
                                             warn = (uu___147_10295.warn);
                                             cache = (uu___147_10295.cache);
                                             nolabels =
                                               (uu___147_10295.nolabels);
                                             use_zfuel_name =
                                               (uu___147_10295.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___147_10295.current_module_name)
                                           } in
                                         let uu____10296 =
                                           let uu____10297 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10297 in
                                         if uu____10296
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10291 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10307::uu____10308 ->
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
                                                   let uu____10331 =
                                                     let uu____10337 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10337) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10331 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10351 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10353 =
                                             match formals with
                                             | [] ->
                                                 let uu____10362 =
                                                   let uu____10363 =
                                                     let uu____10365 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_33  ->
                                                          Some _0_33)
                                                       uu____10365 in
                                                   push_free_var env1 lid
                                                     vname uu____10363 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10362)
                                             | uu____10368 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10373 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10373 in
                                                 let name_tok_corr =
                                                   let uu____10375 =
                                                     let uu____10379 =
                                                       let uu____10380 =
                                                         let uu____10386 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10386) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10380 in
                                                     (uu____10379,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10375 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10353 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10270 with
                                      | (decls2,env2) ->
                                          let uu____10410 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10415 =
                                              encode_term res_t1 env' in
                                            match uu____10415 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10423 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10423,
                                                  decls) in
                                          (match uu____10410 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10431 =
                                                   let uu____10435 =
                                                     let uu____10436 =
                                                       let uu____10442 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10442) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10436 in
                                                   (uu____10435,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10431 in
                                               let freshness =
                                                 let uu____10451 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10451
                                                 then
                                                   let uu____10454 =
                                                     let uu____10455 =
                                                       let uu____10461 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10467 =
                                                         varops.next_id () in
                                                       (vname, uu____10461,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10467) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10455 in
                                                   let uu____10469 =
                                                     let uu____10471 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10471] in
                                                   uu____10454 :: uu____10469
                                                 else [] in
                                               let g =
                                                 let uu____10475 =
                                                   let uu____10477 =
                                                     let uu____10479 =
                                                       let uu____10481 =
                                                         let uu____10483 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10483 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10481 in
                                                     FStar_List.append decls3
                                                       uu____10479 in
                                                   FStar_List.append decls2
                                                     uu____10477 in
                                                 FStar_List.append decls11
                                                   uu____10475 in
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
          let uu____10505 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10505 with
          | None  ->
              let uu____10528 = encode_free_var env x t t_norm [] in
              (match uu____10528 with
               | (decls,env1) ->
                   let uu____10543 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10543 with
                    | (n1,x',uu____10562) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10574) -> ((n1, x1), [], env)
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
          let uu____10607 = encode_free_var env lid t tt quals in
          match uu____10607 with
          | (decls,env1) ->
              let uu____10618 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10618
              then
                let uu____10622 =
                  let uu____10624 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10624 in
                (uu____10622, env1)
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
             (fun uu____10652  ->
                fun lb  ->
                  match uu____10652 with
                  | (decls,env1) ->
                      let uu____10664 =
                        let uu____10668 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10668
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10664 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10682 = FStar_Syntax_Util.head_and_args t in
    match uu____10682 with
    | (hd1,args) ->
        let uu____10708 =
          let uu____10709 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10709.FStar_Syntax_Syntax.n in
        (match uu____10708 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10713,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10726 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10741  ->
      fun quals  ->
        match uu____10741 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10790 = FStar_Util.first_N nbinders formals in
              match uu____10790 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10830  ->
                         fun uu____10831  ->
                           match (uu____10830, uu____10831) with
                           | ((formal,uu____10841),(binder,uu____10843)) ->
                               let uu____10848 =
                                 let uu____10853 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10853) in
                               FStar_Syntax_Syntax.NT uu____10848) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10858 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10872  ->
                              match uu____10872 with
                              | (x,i) ->
                                  let uu____10879 =
                                    let uu___148_10880 = x in
                                    let uu____10881 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___148_10880.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___148_10880.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10881
                                    } in
                                  (uu____10879, i))) in
                    FStar_All.pipe_right uu____10858
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10893 =
                      let uu____10895 =
                        let uu____10896 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10896.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_34  -> Some _0_34)
                        uu____10895 in
                    let uu____10900 =
                      let uu____10901 = FStar_Syntax_Subst.compress body in
                      let uu____10902 =
                        let uu____10903 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10903 in
                      FStar_Syntax_Syntax.extend_app_n uu____10901
                        uu____10902 in
                    uu____10900 uu____10893 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10945 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10945
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___149_10946 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___149_10946.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___149_10946.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___149_10946.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___149_10946.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___149_10946.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___149_10946.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___149_10946.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___149_10946.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___149_10946.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___149_10946.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___149_10946.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___149_10946.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___149_10946.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___149_10946.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___149_10946.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___149_10946.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___149_10946.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___149_10946.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___149_10946.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___149_10946.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___149_10946.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___149_10946.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___149_10946.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10967 = FStar_Syntax_Util.abs_formals e in
                match uu____10967 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11016::uu____11017 ->
                         let uu____11025 =
                           let uu____11026 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11026.FStar_Syntax_Syntax.n in
                         (match uu____11025 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11053 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11053 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11079 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11079
                                   then
                                     let uu____11097 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11097 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11143  ->
                                                   fun uu____11144  ->
                                                     match (uu____11143,
                                                             uu____11144)
                                                     with
                                                     | ((x,uu____11154),
                                                        (b,uu____11156)) ->
                                                         let uu____11161 =
                                                           let uu____11166 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11166) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11161)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11168 =
                                            let uu____11179 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11179) in
                                          (uu____11168, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11214 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11214 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11266) ->
                              let uu____11271 =
                                let uu____11282 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11282 in
                              (uu____11271, true)
                          | uu____11315 when Prims.op_Negation norm1 ->
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
                          | uu____11317 ->
                              let uu____11318 =
                                let uu____11319 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11320 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11319
                                  uu____11320 in
                              failwith uu____11318)
                     | uu____11333 ->
                         let uu____11334 =
                           let uu____11335 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11335.FStar_Syntax_Syntax.n in
                         (match uu____11334 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11362 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11362 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11380 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11380 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11428 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11456 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11456
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11463 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11504  ->
                            fun lb  ->
                              match uu____11504 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11555 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11555
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11558 =
                                      let uu____11566 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11566
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11558 with
                                    | (tok,decl,env2) ->
                                        let uu____11591 =
                                          let uu____11598 =
                                            let uu____11604 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11604, tok) in
                                          uu____11598 :: toks in
                                        (uu____11591, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11463 with
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
                        | uu____11706 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11711 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11711 vars)
                            else
                              (let uu____11713 =
                                 let uu____11717 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11717) in
                               FStar_SMTEncoding_Util.mkApp uu____11713) in
                      let uu____11722 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___118_11724  ->
                                 match uu___118_11724 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11725 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11728 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11728))) in
                      if uu____11722
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11748;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11750;
                                FStar_Syntax_Syntax.lbeff = uu____11751;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11792 =
                                 let uu____11796 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11796 with
                                 | (tcenv',uu____11807,e_t) ->
                                     let uu____11811 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11818 -> failwith "Impossible" in
                                     (match uu____11811 with
                                      | (e1,t_norm1) ->
                                          ((let uu___152_11827 = env1 in
                                            {
                                              bindings =
                                                (uu___152_11827.bindings);
                                              depth = (uu___152_11827.depth);
                                              tcenv = tcenv';
                                              warn = (uu___152_11827.warn);
                                              cache = (uu___152_11827.cache);
                                              nolabels =
                                                (uu___152_11827.nolabels);
                                              use_zfuel_name =
                                                (uu___152_11827.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___152_11827.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___152_11827.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11792 with
                                | (env',e1,t_norm1) ->
                                    let uu____11834 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11834 with
                                     | ((binders,body,uu____11846,uu____11847),curry)
                                         ->
                                         ((let uu____11854 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11854
                                           then
                                             let uu____11855 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11856 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11855 uu____11856
                                           else ());
                                          (let uu____11858 =
                                             encode_binders None binders env' in
                                           match uu____11858 with
                                           | (vars,guards,env'1,binder_decls,uu____11874)
                                               ->
                                               let body1 =
                                                 let uu____11882 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11882
                                                 then
                                                   reify_body env'1.tcenv
                                                     body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11885 =
                                                 let uu____11890 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11890
                                                 then
                                                   let uu____11896 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11897 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11896, uu____11897)
                                                 else
                                                   (let uu____11903 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11903)) in
                                               (match uu____11885 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11917 =
                                                        let uu____11921 =
                                                          let uu____11922 =
                                                            let uu____11928 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11928) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11922 in
                                                        let uu____11934 =
                                                          let uu____11936 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11936 in
                                                        (uu____11921,
                                                          uu____11934,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11917 in
                                                    let uu____11938 =
                                                      let uu____11940 =
                                                        let uu____11942 =
                                                          let uu____11944 =
                                                            let uu____11946 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11946 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11944 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11942 in
                                                      FStar_List.append
                                                        decls1 uu____11940 in
                                                    (uu____11938, env1))))))
                           | uu____11949 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11968 = varops.fresh "fuel" in
                             (uu____11968, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11971 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12010  ->
                                     fun uu____12011  ->
                                       match (uu____12010, uu____12011) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12093 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12093 in
                                           let gtok =
                                             let uu____12095 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12095 in
                                           let env3 =
                                             let uu____12097 =
                                               let uu____12099 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_35  -> Some _0_35)
                                                 uu____12099 in
                                             push_free_var env2 flid gtok
                                               uu____12097 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11971 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12185
                                 t_norm uu____12187 =
                                 match (uu____12185, uu____12187) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12214;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12215;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12232 =
                                       let uu____12236 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12236 with
                                       | (tcenv',uu____12251,e_t) ->
                                           let uu____12255 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12262 ->
                                                 failwith "Impossible" in
                                           (match uu____12255 with
                                            | (e1,t_norm1) ->
                                                ((let uu___153_12271 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___153_12271.bindings);
                                                    depth =
                                                      (uu___153_12271.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___153_12271.warn);
                                                    cache =
                                                      (uu___153_12271.cache);
                                                    nolabels =
                                                      (uu___153_12271.nolabels);
                                                    use_zfuel_name =
                                                      (uu___153_12271.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___153_12271.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___153_12271.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12232 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12281 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12281
                                            then
                                              let uu____12282 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12283 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12284 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12282 uu____12283
                                                uu____12284
                                            else ());
                                           (let uu____12286 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12286 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12308 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12308
                                                  then
                                                    let uu____12309 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12310 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12311 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12312 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12309 uu____12310
                                                      uu____12311 uu____12312
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12316 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12316 with
                                                  | (vars,guards,env'1,binder_decls,uu____12334)
                                                      ->
                                                      let decl_g =
                                                        let uu____12342 =
                                                          let uu____12348 =
                                                            let uu____12350 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12350 in
                                                          (g, uu____12348,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12342 in
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
                                                        let uu____12365 =
                                                          let uu____12369 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12369) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12365 in
                                                      let gsapp =
                                                        let uu____12375 =
                                                          let uu____12379 =
                                                            let uu____12381 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12381 ::
                                                              vars_tm in
                                                          (g, uu____12379) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12375 in
                                                      let gmax =
                                                        let uu____12385 =
                                                          let uu____12389 =
                                                            let uu____12391 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12391 ::
                                                              vars_tm in
                                                          (g, uu____12389) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12385 in
                                                      let body1 =
                                                        let uu____12395 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12395
                                                        then
                                                          reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12397 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12397 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12408
                                                               =
                                                               let uu____12412
                                                                 =
                                                                 let uu____12413
                                                                   =
                                                                   let uu____12421
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (gsapp,
                                                                    body_tm) in
                                                                   ([[gsapp]],
                                                                    (Some
                                                                    (Prims.parse_int
                                                                    "0")),
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12421) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12413 in
                                                               let uu____12432
                                                                 =
                                                                 let uu____12434
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12434 in
                                                               (uu____12412,
                                                                 uu____12432,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12408 in
                                                           let eqn_f =
                                                             let uu____12437
                                                               =
                                                               let uu____12441
                                                                 =
                                                                 let uu____12442
                                                                   =
                                                                   let uu____12448
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12448) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12442 in
                                                               (uu____12441,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12437 in
                                                           let eqn_g' =
                                                             let uu____12456
                                                               =
                                                               let uu____12460
                                                                 =
                                                                 let uu____12461
                                                                   =
                                                                   let uu____12467
                                                                    =
                                                                    let uu____12468
                                                                    =
                                                                    let uu____12471
                                                                    =
                                                                    let uu____12472
                                                                    =
                                                                    let uu____12476
                                                                    =
                                                                    let uu____12478
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12478
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12476) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12472 in
                                                                    (gsapp,
                                                                    uu____12471) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12468 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12467) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12461 in
                                                               (uu____12460,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12456 in
                                                           let uu____12490 =
                                                             let uu____12495
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12495
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12512)
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
                                                                    let uu____12527
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12527
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12530
                                                                    =
                                                                    let uu____12534
                                                                    =
                                                                    let uu____12535
                                                                    =
                                                                    let uu____12541
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12541) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12535 in
                                                                    (uu____12534,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12530 in
                                                                 let uu____12552
                                                                   =
                                                                   let uu____12556
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12556
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12564
                                                                    =
                                                                    let uu____12566
                                                                    =
                                                                    let uu____12567
                                                                    =
                                                                    let uu____12571
                                                                    =
                                                                    let uu____12572
                                                                    =
                                                                    let uu____12578
                                                                    =
                                                                    let uu____12579
                                                                    =
                                                                    let uu____12582
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12582,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12579 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12578) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12572 in
                                                                    (uu____12571,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12567 in
                                                                    [uu____12566] in
                                                                    (d3,
                                                                    uu____12564) in
                                                                 (match uu____12552
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12490
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
                               let uu____12617 =
                                 let uu____12624 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12660  ->
                                      fun uu____12661  ->
                                        match (uu____12660, uu____12661) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12747 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12747 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12624 in
                               (match uu____12617 with
                                | (decls2,eqns,env01) ->
                                    let uu____12787 =
                                      let isDeclFun uu___119_12795 =
                                        match uu___119_12795 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12796 -> true
                                        | uu____12802 -> false in
                                      let uu____12803 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12803
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12787 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12830 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12830
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
        let uu____12863 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12863 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12866 = encode_sigelt' env se in
      match uu____12866 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12876 =
                  let uu____12877 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12877 in
                [uu____12876]
            | uu____12878 ->
                let uu____12879 =
                  let uu____12881 =
                    let uu____12882 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12882 in
                  uu____12881 :: g in
                let uu____12883 =
                  let uu____12885 =
                    let uu____12886 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12886 in
                  [uu____12885] in
                FStar_List.append uu____12879 uu____12883 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12894 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12903 =
            let uu____12904 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12904 Prims.op_Negation in
          if uu____12903
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12924 ->
                   let uu____12925 =
                     let uu____12928 =
                       let uu____12929 =
                         let uu____12944 =
                           FStar_All.pipe_left (fun _0_36  -> Some _0_36)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12944) in
                       FStar_Syntax_Syntax.Tm_abs uu____12929 in
                     FStar_Syntax_Syntax.mk uu____12928 in
                   uu____12925 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12997 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12997 with
               | (aname,atok,env2) ->
                   let uu____13007 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13007 with
                    | (formals,uu____13017) ->
                        let uu____13024 =
                          let uu____13027 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13027 env2 in
                        (match uu____13024 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13035 =
                                 let uu____13036 =
                                   let uu____13042 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13050  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13042,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13036 in
                               [uu____13035;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13057 =
                               let aux uu____13086 uu____13087 =
                                 match (uu____13086, uu____13087) with
                                 | ((bv,uu____13114),(env3,acc_sorts,acc)) ->
                                     let uu____13135 = gen_term_var env3 bv in
                                     (match uu____13135 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13057 with
                              | (uu____13173,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13187 =
                                      let uu____13191 =
                                        let uu____13192 =
                                          let uu____13198 =
                                            let uu____13199 =
                                              let uu____13202 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13202) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13199 in
                                          ([[app]], xs_sorts, uu____13198) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13192 in
                                      (uu____13191, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13187 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13214 =
                                      let uu____13218 =
                                        let uu____13219 =
                                          let uu____13225 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13225) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13219 in
                                      (uu____13218,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13214 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13235 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13235 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13251,uu____13252)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13253 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13253 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13264,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13269 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___120_13271  ->
                      match uu___120_13271 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13274 -> false)) in
            Prims.op_Negation uu____13269 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13280 = encode_top_level_val env fv t quals in
             match uu____13280 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13292 =
                   let uu____13294 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13294 in
                 (uu____13292, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13299 = encode_formula f env in
          (match uu____13299 with
           | (f1,decls) ->
               let g =
                 let uu____13308 =
                   let uu____13309 =
                     let uu____13313 =
                       let uu____13315 =
                         let uu____13316 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13316 in
                       Some uu____13315 in
                     let uu____13317 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13313, uu____13317) in
                   FStar_SMTEncoding_Util.mkAssume uu____13309 in
                 [uu____13308] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13321,uu____13322) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13328 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13335 =
                       let uu____13340 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13340.FStar_Syntax_Syntax.fv_name in
                     uu____13335.FStar_Syntax_Syntax.v in
                   let uu____13344 =
                     let uu____13345 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13345 in
                   if uu____13344
                   then
                     let val_decl =
                       let uu___154_13360 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___154_13360.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___154_13360.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___154_13360.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13364 = encode_sigelt' env1 val_decl in
                     match uu____13364 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13328 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13381,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13383;
                          FStar_Syntax_Syntax.lbtyp = uu____13384;
                          FStar_Syntax_Syntax.lbeff = uu____13385;
                          FStar_Syntax_Syntax.lbdef = uu____13386;_}::[]),uu____13387,uu____13388)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13402 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13402 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13425 =
                   let uu____13427 =
                     let uu____13428 =
                       let uu____13432 =
                         let uu____13433 =
                           let uu____13439 =
                             let uu____13440 =
                               let uu____13443 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13443) in
                             FStar_SMTEncoding_Util.mkEq uu____13440 in
                           ([[b2t_x]], [xx], uu____13439) in
                         FStar_SMTEncoding_Util.mkForall uu____13433 in
                       (uu____13432, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13428 in
                   [uu____13427] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13425 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13460,uu____13461,uu____13462)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13468  ->
                  match uu___121_13468 with
                  | FStar_Syntax_Syntax.Discriminator uu____13469 -> true
                  | uu____13470 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13472,lids,uu____13474) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13481 =
                     let uu____13482 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13482.FStar_Ident.idText in
                   uu____13481 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___122_13484  ->
                     match uu___122_13484 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13485 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13488,uu____13489)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___123_13499  ->
                  match uu___123_13499 with
                  | FStar_Syntax_Syntax.Projector uu____13500 -> true
                  | uu____13503 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13510 = try_lookup_free_var env l in
          (match uu____13510 with
           | Some uu____13514 -> ([], env)
           | None  ->
               let se1 =
                 let uu___155_13517 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___155_13517.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___155_13517.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13523,uu____13524) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13536) ->
          let uu____13541 = encode_sigelts env ses in
          (match uu____13541 with
           | (g,env1) ->
               let uu____13551 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___124_13561  ->
                         match uu___124_13561 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13562;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13563;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13564;_}
                             -> false
                         | uu____13566 -> true)) in
               (match uu____13551 with
                | (g',inversions) ->
                    let uu____13575 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___125_13585  ->
                              match uu___125_13585 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13586 ->
                                  true
                              | uu____13592 -> false)) in
                    (match uu____13575 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13603,tps,k,uu____13606,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___126_13616  ->
                    match uu___126_13616 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13617 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13624 = c in
              match uu____13624 with
              | (name,args,uu____13628,uu____13629,uu____13630) ->
                  let uu____13633 =
                    let uu____13634 =
                      let uu____13640 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13647  ->
                                match uu____13647 with
                                | (uu____13651,sort,uu____13653) -> sort)) in
                      (name, uu____13640, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13634 in
                  [uu____13633]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13671 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13674 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13674 FStar_Option.isNone)) in
            if uu____13671
            then []
            else
              (let uu____13691 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13691 with
               | (xxsym,xx) ->
                   let uu____13697 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13708  ->
                             fun l  ->
                               match uu____13708 with
                               | (out,decls) ->
                                   let uu____13720 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13720 with
                                    | (uu____13726,data_t) ->
                                        let uu____13728 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13728 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13757 =
                                                 let uu____13758 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13758.FStar_Syntax_Syntax.n in
                                               match uu____13757 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13766,indices) ->
                                                   indices
                                               | uu____13782 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13794  ->
                                                         match uu____13794
                                                         with
                                                         | (x,uu____13798) ->
                                                             let uu____13799
                                                               =
                                                               let uu____13800
                                                                 =
                                                                 let uu____13804
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13804,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13800 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13799)
                                                    env) in
                                             let uu____13806 =
                                               encode_args indices env1 in
                                             (match uu____13806 with
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
                                                      let uu____13826 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13834
                                                                 =
                                                                 let uu____13837
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13837,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13834)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13826
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13839 =
                                                      let uu____13840 =
                                                        let uu____13843 =
                                                          let uu____13844 =
                                                            let uu____13847 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13847,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13844 in
                                                        (out, uu____13843) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13840 in
                                                    (uu____13839,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13697 with
                    | (data_ax,decls) ->
                        let uu____13855 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13855 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13866 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13866 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13869 =
                                 let uu____13873 =
                                   let uu____13874 =
                                     let uu____13880 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13888 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13880,
                                       uu____13888) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13874 in
                                 let uu____13896 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13873, (Some "inversion axiom"),
                                   uu____13896) in
                               FStar_SMTEncoding_Util.mkAssume uu____13869 in
                             let pattern_guarded_inversion =
                               let uu____13900 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13900
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13908 =
                                   let uu____13909 =
                                     let uu____13913 =
                                       let uu____13914 =
                                         let uu____13920 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13928 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13920, uu____13928) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13914 in
                                     let uu____13936 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13913, (Some "inversion axiom"),
                                       uu____13936) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13909 in
                                 [uu____13908]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13939 =
            let uu____13947 =
              let uu____13948 = FStar_Syntax_Subst.compress k in
              uu____13948.FStar_Syntax_Syntax.n in
            match uu____13947 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13977 -> (tps, k) in
          (match uu____13939 with
           | (formals,res) ->
               let uu____13992 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13992 with
                | (formals1,res1) ->
                    let uu____13999 = encode_binders None formals1 env in
                    (match uu____13999 with
                     | (vars,guards,env',binder_decls,uu____14014) ->
                         let uu____14021 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14021 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14034 =
                                  let uu____14038 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14038) in
                                FStar_SMTEncoding_Util.mkApp uu____14034 in
                              let uu____14043 =
                                let tname_decl =
                                  let uu____14049 =
                                    let uu____14050 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14065  ->
                                              match uu____14065 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14073 = varops.next_id () in
                                    (tname, uu____14050,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14073, false) in
                                  constructor_or_logic_type_decl uu____14049 in
                                let uu____14078 =
                                  match vars with
                                  | [] ->
                                      let uu____14085 =
                                        let uu____14086 =
                                          let uu____14088 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_37  -> Some _0_37)
                                            uu____14088 in
                                        push_free_var env1 t tname
                                          uu____14086 in
                                      ([], uu____14085)
                                  | uu____14092 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14098 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14098 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14107 =
                                          let uu____14111 =
                                            let uu____14112 =
                                              let uu____14120 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14120) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14112 in
                                          (uu____14111,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14107 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14078 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14043 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14143 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14143 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14157 =
                                               let uu____14158 =
                                                 let uu____14162 =
                                                   let uu____14163 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14163 in
                                                 (uu____14162,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14158 in
                                             [uu____14157]
                                           else [] in
                                         let uu____14166 =
                                           let uu____14168 =
                                             let uu____14170 =
                                               let uu____14171 =
                                                 let uu____14175 =
                                                   let uu____14176 =
                                                     let uu____14182 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14182) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14176 in
                                                 (uu____14175, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14171 in
                                             [uu____14170] in
                                           FStar_List.append karr uu____14168 in
                                         FStar_List.append decls1 uu____14166 in
                                   let aux =
                                     let uu____14191 =
                                       let uu____14193 =
                                         inversion_axioms tapp vars in
                                       let uu____14195 =
                                         let uu____14197 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14197] in
                                       FStar_List.append uu____14193
                                         uu____14195 in
                                     FStar_List.append kindingAx uu____14191 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14202,uu____14203,uu____14204,uu____14205,uu____14206)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14211,t,uu____14213,n_tps,uu____14215) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14220 = new_term_constant_and_tok_from_lid env d in
          (match uu____14220 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14231 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14231 with
                | (formals,t_res) ->
                    let uu____14253 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14253 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14262 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14262 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14300 =
                                            mk_term_projector_name d x in
                                          (uu____14300,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14302 =
                                  let uu____14312 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14312, true) in
                                FStar_All.pipe_right uu____14302
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
                              let uu____14334 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14334 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14342::uu____14343 ->
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
                                         let uu____14368 =
                                           let uu____14374 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14374) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14368
                                     | uu____14387 -> tok_typing in
                                   let uu____14392 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14392 with
                                    | (vars',guards',env'',decls_formals,uu____14407)
                                        ->
                                        let uu____14414 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14414 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14433 ->
                                                   let uu____14437 =
                                                     let uu____14438 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14438 in
                                                   [uu____14437] in
                                             let encode_elim uu____14445 =
                                               let uu____14446 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14446 with
                                               | (head1,args) ->
                                                   let uu____14475 =
                                                     let uu____14476 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14476.FStar_Syntax_Syntax.n in
                                                   (match uu____14475 with
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
                                                        let uu____14494 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14494
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
                                                                 | uu____14520
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14528
                                                                    =
                                                                    let uu____14529
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14529 in
                                                                    if
                                                                    uu____14528
                                                                    then
                                                                    let uu____14536
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14536]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14538
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14551
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14551
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14573
                                                                    =
                                                                    let uu____14577
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14577 in
                                                                    (match uu____14573
                                                                    with
                                                                    | 
                                                                    (uu____14584,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14590
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14590
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14592
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14592
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
                                                             (match uu____14538
                                                              with
                                                              | (uu____14600,arg_vars,elim_eqns_or_guards,uu____14603)
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
                                                                    let uu____14622
                                                                    =
                                                                    let uu____14626
                                                                    =
                                                                    let uu____14627
                                                                    =
                                                                    let uu____14633
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14639
                                                                    =
                                                                    let uu____14640
                                                                    =
                                                                    let uu____14643
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14643) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14640 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14633,
                                                                    uu____14639) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14627 in
                                                                    (uu____14626,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14622 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14656
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14656,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14658
                                                                    =
                                                                    let uu____14662
                                                                    =
                                                                    let uu____14663
                                                                    =
                                                                    let uu____14669
                                                                    =
                                                                    let uu____14672
                                                                    =
                                                                    let uu____14674
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14674] in
                                                                    [uu____14672] in
                                                                    let uu____14677
                                                                    =
                                                                    let uu____14678
                                                                    =
                                                                    let uu____14681
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14682
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14681,
                                                                    uu____14682) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14678 in
                                                                    (uu____14669,
                                                                    [x],
                                                                    uu____14677) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14663 in
                                                                    let uu____14692
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14662,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14692) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14658
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14697
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
                                                                    (let uu____14712
                                                                    =
                                                                    let uu____14713
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14713
                                                                    dapp1 in
                                                                    [uu____14712]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14697
                                                                    FStar_List.flatten in
                                                                    let uu____14717
                                                                    =
                                                                    let uu____14721
                                                                    =
                                                                    let uu____14722
                                                                    =
                                                                    let uu____14728
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14734
                                                                    =
                                                                    let uu____14735
                                                                    =
                                                                    let uu____14738
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14738) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14735 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14728,
                                                                    uu____14734) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14722 in
                                                                    (uu____14721,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14717) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14748 ->
                                                        ((let uu____14750 =
                                                            let uu____14751 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14752 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14751
                                                              uu____14752 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14750);
                                                         ([], []))) in
                                             let uu____14755 = encode_elim () in
                                             (match uu____14755 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14767 =
                                                      let uu____14769 =
                                                        let uu____14771 =
                                                          let uu____14773 =
                                                            let uu____14775 =
                                                              let uu____14776
                                                                =
                                                                let uu____14782
                                                                  =
                                                                  let uu____14784
                                                                    =
                                                                    let uu____14785
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14785 in
                                                                  Some
                                                                    uu____14784 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14782) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14776 in
                                                            [uu____14775] in
                                                          let uu____14788 =
                                                            let uu____14790 =
                                                              let uu____14792
                                                                =
                                                                let uu____14794
                                                                  =
                                                                  let uu____14796
                                                                    =
                                                                    let uu____14798
                                                                    =
                                                                    let uu____14800
                                                                    =
                                                                    let uu____14801
                                                                    =
                                                                    let uu____14805
                                                                    =
                                                                    let uu____14806
                                                                    =
                                                                    let uu____14812
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14812) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14806 in
                                                                    (uu____14805,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14801 in
                                                                    let uu____14819
                                                                    =
                                                                    let uu____14821
                                                                    =
                                                                    let uu____14822
                                                                    =
                                                                    let uu____14826
                                                                    =
                                                                    let uu____14827
                                                                    =
                                                                    let uu____14833
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14839
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14833,
                                                                    uu____14839) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14827 in
                                                                    (uu____14826,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14822 in
                                                                    [uu____14821] in
                                                                    uu____14800
                                                                    ::
                                                                    uu____14819 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14798 in
                                                                  FStar_List.append
                                                                    uu____14796
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14794 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14792 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14790 in
                                                          FStar_List.append
                                                            uu____14773
                                                            uu____14788 in
                                                        FStar_List.append
                                                          decls3 uu____14771 in
                                                      FStar_List.append
                                                        decls2 uu____14769 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14767 in
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
           (fun uu____14860  ->
              fun se  ->
                match uu____14860 with
                | (g,env1) ->
                    let uu____14872 = encode_sigelt env1 se in
                    (match uu____14872 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14908 =
        match uu____14908 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14926 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14931 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14931
                   then
                     let uu____14932 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14933 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14934 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14932 uu____14933 uu____14934
                   else ());
                  (let uu____14936 = encode_term t1 env1 in
                   match uu____14936 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14946 =
                         let uu____14950 =
                           let uu____14951 =
                             let uu____14952 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14952
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14951 in
                         new_term_constant_from_string env1 x uu____14950 in
                       (match uu____14946 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14963 = FStar_Options.log_queries () in
                              if uu____14963
                              then
                                let uu____14965 =
                                  let uu____14966 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14967 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14968 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14966 uu____14967 uu____14968 in
                                Some uu____14965
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14979,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14988 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14988 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15007 = encode_sigelt env1 se in
                 (match uu____15007 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15017 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15017 with | (uu____15029,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15074  ->
            match uu____15074 with
            | (l,uu____15081,uu____15082) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15103  ->
            match uu____15103 with
            | (l,uu____15111,uu____15112) ->
                let uu____15117 =
                  FStar_All.pipe_left
                    (fun _0_38  -> FStar_SMTEncoding_Term.Echo _0_38)
                    (Prims.fst l) in
                let uu____15118 =
                  let uu____15120 =
                    let uu____15121 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15121 in
                  [uu____15120] in
                uu____15117 :: uu____15118)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15132 =
      let uu____15134 =
        let uu____15135 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15137 =
          let uu____15138 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15138 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15135;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15137
        } in
      [uu____15134] in
    FStar_ST.write last_env uu____15132
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15148 = FStar_ST.read last_env in
      match uu____15148 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15154 ->
          let uu___156_15156 = e in
          let uu____15157 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___156_15156.bindings);
            depth = (uu___156_15156.depth);
            tcenv;
            warn = (uu___156_15156.warn);
            cache = (uu___156_15156.cache);
            nolabels = (uu___156_15156.nolabels);
            use_zfuel_name = (uu___156_15156.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___156_15156.encode_non_total_function_typ);
            current_module_name = uu____15157
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15161 = FStar_ST.read last_env in
    match uu____15161 with
    | [] -> failwith "Empty env stack"
    | uu____15166::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15174  ->
    let uu____15175 = FStar_ST.read last_env in
    match uu____15175 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___157_15186 = hd1 in
          {
            bindings = (uu___157_15186.bindings);
            depth = (uu___157_15186.depth);
            tcenv = (uu___157_15186.tcenv);
            warn = (uu___157_15186.warn);
            cache = refs;
            nolabels = (uu___157_15186.nolabels);
            use_zfuel_name = (uu___157_15186.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___157_15186.encode_non_total_function_typ);
            current_module_name = (uu___157_15186.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15192  ->
    let uu____15193 = FStar_ST.read last_env in
    match uu____15193 with
    | [] -> failwith "Popping an empty stack"
    | uu____15198::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15206  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15209  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15212  ->
    let uu____15213 = FStar_ST.read last_env in
    match uu____15213 with
    | hd1::uu____15219::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15225 -> failwith "Impossible"
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
        | (uu____15274::uu____15275,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___158_15279 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___158_15279.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___158_15279.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___158_15279.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15280 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15291 =
        let uu____15293 =
          let uu____15294 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15294 in
        let uu____15295 = open_fact_db_tags env in uu____15293 :: uu____15295 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15291
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
      let uu____15310 = encode_sigelt env se in
      match uu____15310 with
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
        let uu____15335 = FStar_Options.log_queries () in
        if uu____15335
        then
          let uu____15337 =
            let uu____15338 =
              let uu____15339 =
                let uu____15340 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15340 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15339 in
            FStar_SMTEncoding_Term.Caption uu____15338 in
          uu____15337 :: decls
        else decls in
      let env =
        let uu____15347 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15347 tcenv in
      let uu____15348 = encode_top_level_facts env se in
      match uu____15348 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15357 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15357))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15368 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15368
       then
         let uu____15369 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15369
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15390  ->
                 fun se  ->
                   match uu____15390 with
                   | (g,env2) ->
                       let uu____15402 = encode_top_level_facts env2 se in
                       (match uu____15402 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15415 =
         encode_signature
           (let uu___159_15419 = env in
            {
              bindings = (uu___159_15419.bindings);
              depth = (uu___159_15419.depth);
              tcenv = (uu___159_15419.tcenv);
              warn = false;
              cache = (uu___159_15419.cache);
              nolabels = (uu___159_15419.nolabels);
              use_zfuel_name = (uu___159_15419.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___159_15419.encode_non_total_function_typ);
              current_module_name = (uu___159_15419.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15415 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15431 = FStar_Options.log_queries () in
             if uu____15431
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___160_15436 = env1 in
               {
                 bindings = (uu___160_15436.bindings);
                 depth = (uu___160_15436.depth);
                 tcenv = (uu___160_15436.tcenv);
                 warn = true;
                 cache = (uu___160_15436.cache);
                 nolabels = (uu___160_15436.nolabels);
                 use_zfuel_name = (uu___160_15436.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___160_15436.encode_non_total_function_typ);
                 current_module_name = (uu___160_15436.current_module_name)
               });
            (let uu____15438 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15438
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
        (let uu____15473 =
           let uu____15474 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15474.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15473);
        (let env =
           let uu____15476 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15476 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15483 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15504 = aux rest in
                 (match uu____15504 with
                  | (out,rest1) ->
                      let t =
                        let uu____15522 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15522 with
                        | Some uu____15526 ->
                            let uu____15527 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15527
                              x.FStar_Syntax_Syntax.sort
                        | uu____15528 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15531 =
                        let uu____15533 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___161_15534 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___161_15534.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___161_15534.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15533 :: out in
                      (uu____15531, rest1))
             | uu____15537 -> ([], bindings1) in
           let uu____15541 = aux bindings in
           match uu____15541 with
           | (closing,bindings1) ->
               let uu____15555 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15555, bindings1) in
         match uu____15483 with
         | (q1,bindings1) ->
             let uu____15568 =
               let uu____15571 =
                 FStar_List.filter
                   (fun uu___127_15573  ->
                      match uu___127_15573 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15574 ->
                          false
                      | uu____15578 -> true) bindings1 in
               encode_env_bindings env uu____15571 in
             (match uu____15568 with
              | (env_decls,env1) ->
                  ((let uu____15589 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15589
                    then
                      let uu____15590 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15590
                    else ());
                   (let uu____15592 = encode_formula q1 env1 in
                    match uu____15592 with
                    | (phi,qdecls) ->
                        let uu____15604 =
                          let uu____15607 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15607 phi in
                        (match uu____15604 with
                         | (labels,phi1) ->
                             let uu____15617 = encode_labels labels in
                             (match uu____15617 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15638 =
                                      let uu____15642 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15643 =
                                        varops.mk_unique "@query" in
                                      (uu____15642, (Some "query"),
                                        uu____15643) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15638 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15656 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15656 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15658 = encode_formula q env in
       match uu____15658 with
       | (f,uu____15662) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15664) -> true
             | uu____15667 -> false)))