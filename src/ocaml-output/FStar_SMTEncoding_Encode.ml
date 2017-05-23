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
    let uu___127_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___127_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___127_780.FStar_Syntax_Syntax.sort)
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
      (Prims.string* FStar_SMTEncoding_Term.term* env_t)
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
      Prims.string -> (Prims.string* FStar_SMTEncoding_Term.term* env_t)
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
        let uu___132_1182 = env in
        let uu____1183 =
          let uu____1185 =
            let uu____1186 =
              let uu____1193 =
                let uu____1195 = FStar_SMTEncoding_Util.mkApp (ftok, []) in
                FStar_All.pipe_left (fun _0_29  -> Some _0_29) uu____1195 in
              (x, fname, uu____1193, None) in
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
      (Prims.string* FStar_SMTEncoding_Term.term Prims.option*
        FStar_SMTEncoding_Term.term Prims.option) Prims.option
  =
  fun env  ->
    fun a  ->
      lookup_binding env
        (fun uu___105_1217  ->
           match uu___105_1217 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1239 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1251 =
        lookup_binding env
          (fun uu___106_1253  ->
             match uu___106_1253 with
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
          let uu___133_1325 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
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
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
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
                           FStar_All.pipe_left (fun _0_30  -> Some _0_30)
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
        (fun uu___107_1538  ->
           match uu___107_1538 with
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
               (fun uu___108_1723  ->
                  match uu___108_1723 with
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
  fun uu___109_1828  ->
    match uu___109_1828 with
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
    | uu____1982 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_1985  ->
    match uu___110_1985 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____1987 =
          let uu____1991 =
            let uu____1993 =
              let uu____1994 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____1994 in
            [uu____1993] in
          ("FStar.Char.Char", uu____1991) in
        FStar_SMTEncoding_Util.mkApp uu____1987
    | FStar_Const.Const_int (i,None ) ->
        let uu____2002 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2002
    | FStar_Const.Const_int (i,Some uu____2004) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2013) ->
        let uu____2016 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2016
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2020 =
          let uu____2021 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2021 in
        failwith uu____2020
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2040 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2048 ->
            let uu____2053 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2053
        | uu____2054 ->
            if norm1
            then let uu____2055 = whnf env t1 in aux false uu____2055
            else
              (let uu____2057 =
                 let uu____2058 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2059 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2058 uu____2059 in
               failwith uu____2057) in
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
    | uu____2080 ->
        let uu____2081 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2081)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2109::uu____2110::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2113::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2115 -> false
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
        (let uu____2260 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2260
         then
           let uu____2261 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2261
         else ());
        (let uu____2263 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2299  ->
                   fun b  ->
                     match uu____2299 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2342 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2351 = gen_term_var env1 x in
                           match uu____2351 with
                           | (xxsym,xx,env') ->
                               let uu____2365 =
                                 let uu____2368 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2368 env1 xx in
                               (match uu____2365 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2342 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2263 with
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
          let uu____2456 = encode_term t env in
          match uu____2456 with
          | (t1,decls) ->
              let uu____2463 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2463, decls)
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
          let uu____2471 = encode_term t env in
          match uu____2471 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2480 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2480, decls)
               | Some f ->
                   let uu____2482 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2482, decls))
and encode_arith_term:
  env_t ->
    (FStar_Syntax_Syntax.term',FStar_Syntax_Syntax.term')
      FStar_Syntax_Syntax.syntax ->
      FStar_Syntax_Syntax.args ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun env  ->
    fun head1  ->
      fun args_e  ->
        let uu____2488 = encode_args args_e env in
        match uu____2488 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2500 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2507 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2507 in
            let binary arg_tms1 =
              let uu____2516 =
                let uu____2517 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2517 in
              let uu____2518 =
                let uu____2519 =
                  let uu____2520 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2520 in
                FStar_SMTEncoding_Term.unboxInt uu____2519 in
              (uu____2516, uu____2518) in
            let mk_default uu____2525 =
              let uu____2526 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2526 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2571 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2571
              then
                let uu____2572 = let uu____2573 = mk_args ts in op uu____2573 in
                FStar_All.pipe_right uu____2572 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2596 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2596
              then
                let uu____2597 = binary ts in
                match uu____2597 with
                | (t1,t2) ->
                    let uu____2602 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2602
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2605 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2605
                 then
                   let uu____2606 = op (binary ts) in
                   FStar_All.pipe_right uu____2606
                     FStar_SMTEncoding_Term.boxInt
                 else mk_default ()) in
            let add1 = mk_l FStar_SMTEncoding_Util.mkAdd binary in
            let sub1 = mk_l FStar_SMTEncoding_Util.mkSub binary in
            let minus = mk_l FStar_SMTEncoding_Util.mkMinus unary in
            let mul1 = mk_nl "_mul" FStar_SMTEncoding_Util.mkMul in
            let div1 = mk_nl "_div" FStar_SMTEncoding_Util.mkDiv in
            let modulus = mk_nl "_mod" FStar_SMTEncoding_Util.mkMod in
            let ops =
              [(FStar_Syntax_Const.op_Addition, add1);
              (FStar_Syntax_Const.op_Subtraction, sub1);
              (FStar_Syntax_Const.op_Multiply, mul1);
              (FStar_Syntax_Const.op_Division, div1);
              (FStar_Syntax_Const.op_Modulus, modulus);
              (FStar_Syntax_Const.op_Minus, minus)] in
            let uu____2696 =
              let uu____2702 =
                FStar_List.tryFind
                  (fun uu____2714  ->
                     match uu____2714 with
                     | (l,uu____2721) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2702 FStar_Util.must in
            (match uu____2696 with
             | (uu____2746,op) ->
                 let uu____2754 = op arg_tms in (uu____2754, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2761 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2761
       then
         let uu____2762 = FStar_Syntax_Print.tag_of_term t in
         let uu____2763 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2764 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2762 uu____2763
           uu____2764
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2769 =
             let uu____2770 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2771 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2772 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2773 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2770
               uu____2771 uu____2772 uu____2773 in
           failwith uu____2769
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2777 =
             let uu____2778 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2778 in
           failwith uu____2777
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2783) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2813) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2822 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2822, [])
       | FStar_Syntax_Syntax.Tm_type uu____2828 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2831) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2837 = encode_const c in (uu____2837, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2852 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2852 with
            | (binders1,res) ->
                let uu____2859 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2859
                then
                  let uu____2862 = encode_binders None binders1 env in
                  (match uu____2862 with
                   | (vars,guards,env',decls,uu____2877) ->
                       let fsym =
                         let uu____2887 = varops.fresh "f" in
                         (uu____2887, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2890 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2894 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2894.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2894.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2894.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2894.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2894.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2894.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2894.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2894.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2894.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2894.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2894.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2894.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2894.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2894.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2894.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2894.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2894.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2894.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2894.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2894.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2894.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2894.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2894.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2890 with
                        | (pre_opt,res_t) ->
                            let uu____2901 =
                              encode_term_pred None res_t env' app in
                            (match uu____2901 with
                             | (res_pred,decls') ->
                                 let uu____2908 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2915 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2915, [])
                                   | Some pre ->
                                       let uu____2918 =
                                         encode_formula pre env' in
                                       (match uu____2918 with
                                        | (guard,decls0) ->
                                            let uu____2926 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2926, decls0)) in
                                 (match uu____2908 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2934 =
                                          let uu____2940 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2940) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2934 in
                                      let cvars =
                                        let uu____2950 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2950
                                          (FStar_List.filter
                                             (fun uu____2956  ->
                                                match uu____2956 with
                                                | (x,uu____2960) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2971 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2971 with
                                       | Some cache_entry ->
                                           let uu____2976 =
                                             let uu____2977 =
                                               let uu____2981 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2981) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2977 in
                                           (uu____2976,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____2992 =
                                               let uu____2993 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2993 in
                                             varops.mk_unique uu____2992 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____3000 =
                                               FStar_Options.log_queries () in
                                             if uu____3000
                                             then
                                               let uu____3002 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3002
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3008 =
                                               let uu____3012 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3012) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3008 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3020 =
                                               let uu____3024 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3024, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3020 in
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
                                             let uu____3037 =
                                               let uu____3041 =
                                                 let uu____3042 =
                                                   let uu____3048 =
                                                     let uu____3049 =
                                                       let uu____3052 =
                                                         let uu____3053 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3053 in
                                                       (f_has_t, uu____3052) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3049 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3048) in
                                                 mkForall_fuel uu____3042 in
                                               (uu____3041,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3037 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3066 =
                                               let uu____3070 =
                                                 let uu____3071 =
                                                   let uu____3077 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3077) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3071 in
                                               (uu____3070, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3066 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3091 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3091);
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
                     let uu____3102 =
                       let uu____3106 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3106, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3102 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3115 =
                       let uu____3119 =
                         let uu____3120 =
                           let uu____3126 =
                             let uu____3127 =
                               let uu____3130 =
                                 let uu____3131 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3131 in
                               (f_has_t, uu____3130) in
                             FStar_SMTEncoding_Util.mkImp uu____3127 in
                           ([[f_has_t]], [fsym], uu____3126) in
                         mkForall_fuel uu____3120 in
                       (uu____3119, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3115 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3145 ->
           let uu____3150 =
             let uu____3153 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3153 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3158;
                 FStar_Syntax_Syntax.pos = uu____3159;
                 FStar_Syntax_Syntax.vars = uu____3160;_} ->
                 let uu____3167 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3167 with
                  | (b,f1) ->
                      let uu____3181 =
                        let uu____3182 = FStar_List.hd b in
                        Prims.fst uu____3182 in
                      (uu____3181, f1))
             | uu____3187 -> failwith "impossible" in
           (match uu____3150 with
            | (x,f) ->
                let uu____3194 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3194 with
                 | (base_t,decls) ->
                     let uu____3201 = gen_term_var env x in
                     (match uu____3201 with
                      | (x1,xtm,env') ->
                          let uu____3210 = encode_formula f env' in
                          (match uu____3210 with
                           | (refinement,decls') ->
                               let uu____3217 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3217 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3228 =
                                        let uu____3230 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3234 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3230
                                          uu____3234 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3228 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3250  ->
                                              match uu____3250 with
                                              | (y,uu____3254) ->
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
                                    let uu____3273 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3273 with
                                     | Some cache_entry ->
                                         let uu____3278 =
                                           let uu____3279 =
                                             let uu____3283 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3283) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3279 in
                                         (uu____3278,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3295 =
                                             let uu____3296 =
                                               let uu____3297 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3297 in
                                             Prims.strcat module_name
                                               uu____3296 in
                                           varops.mk_unique uu____3295 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3306 =
                                             let uu____3310 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3310) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3306 in
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
                                           let uu____3320 =
                                             let uu____3324 =
                                               let uu____3325 =
                                                 let uu____3331 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3331) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3325 in
                                             (uu____3324,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3320 in
                                         let t_kinding =
                                           let uu____3341 =
                                             let uu____3345 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3345,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3341 in
                                         let t_interp =
                                           let uu____3355 =
                                             let uu____3359 =
                                               let uu____3360 =
                                                 let uu____3366 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3366) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3360 in
                                             let uu____3378 =
                                               let uu____3380 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3380 in
                                             (uu____3359, uu____3378,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3355 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3385 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3385);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3402 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3402 in
           let uu____3406 = encode_term_pred None k env ttm in
           (match uu____3406 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3414 =
                    let uu____3418 =
                      let uu____3419 =
                        let uu____3420 =
                          let uu____3421 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3421 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3420 in
                      varops.mk_unique uu____3419 in
                    (t_has_k, (Some "Uvar typing"), uu____3418) in
                  FStar_SMTEncoding_Util.mkAssume uu____3414 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3427 ->
           let uu____3437 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3437 with
            | (head1,args_e) ->
                let uu____3465 =
                  let uu____3473 =
                    let uu____3474 = FStar_Syntax_Subst.compress head1 in
                    uu____3474.FStar_Syntax_Syntax.n in
                  (uu____3473, args_e) in
                (match uu____3465 with
                 | uu____3484 when head_redex env head1 ->
                     let uu____3492 = whnf env t in
                     encode_term uu____3492 env
                 | uu____3493 when is_arithmetic_primitive head1 args_e ->
                     encode_arith_term env head1 args_e
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
                     let uu____3578 = encode_term v1 env in
                     (match uu____3578 with
                      | (v11,decls1) ->
                          let uu____3585 = encode_term v2 env in
                          (match uu____3585 with
                           | (v21,decls2) ->
                               let uu____3592 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3592,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3594) ->
                     let e0 =
                       let uu____3606 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3606 in
                     ((let uu____3612 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3612
                       then
                         let uu____3613 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3613
                       else ());
                      (let e =
                         let uu____3618 =
                           let uu____3619 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3620 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3619
                             uu____3620 in
                         uu____3618 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3629),(arg,uu____3631)::[]) -> encode_term arg env
                 | uu____3649 ->
                     let uu____3657 = encode_args args_e env in
                     (match uu____3657 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3690 = encode_term head1 env in
                            match uu____3690 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3729 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3729 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3771  ->
                                                 fun uu____3772  ->
                                                   match (uu____3771,
                                                           uu____3772)
                                                   with
                                                   | ((bv,uu____3786),
                                                      (a,uu____3788)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3802 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3802
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3807 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3807 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3817 =
                                                   let uu____3821 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3826 =
                                                     let uu____3827 =
                                                       let uu____3828 =
                                                         let uu____3829 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3829 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3828 in
                                                     varops.mk_unique
                                                       uu____3827 in
                                                   (uu____3821,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3826) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3817 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3846 = lookup_free_var_sym env fv in
                            match uu____3846 with
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
                                let uu____3884 =
                                  let uu____3885 =
                                    let uu____3888 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3888 Prims.fst in
                                  FStar_All.pipe_right uu____3885 Prims.snd in
                                Some uu____3884
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3907,(FStar_Util.Inl t1,uu____3909),uu____3910)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3948,(FStar_Util.Inr c,uu____3950),uu____3951)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3989 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____4009 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____4009 in
                               let uu____4010 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____4010 with
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
                                     | uu____4035 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4080 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4080 with
            | (bs1,body1,opening) ->
                let fallback uu____4095 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4100 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4100, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4111 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4111
                  | FStar_Util.Inr (eff,uu____4113) ->
                      let uu____4119 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4119 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4164 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4165 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4165.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4165.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4165.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4165.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4165.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4165.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4165.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4165.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4165.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4165.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4165.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4165.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4165.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4165.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4165.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4165.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4165.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4165.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4165.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4165.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4165.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4165.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4165.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4164 FStar_Syntax_Syntax.U_unknown in
                        let uu____4166 =
                          let uu____4167 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4167 in
                        FStar_Util.Inl uu____4166
                    | FStar_Util.Inr (eff_name,uu____4174) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4205 =
                        let uu____4206 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4206 in
                      FStar_All.pipe_right uu____4205
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4218 =
                        let uu____4219 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4219 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4227 =
                          let uu____4228 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4228 in
                        FStar_All.pipe_right uu____4227
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4232 =
                             let uu____4233 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4233 in
                           FStar_All.pipe_right uu____4232
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4244 =
                         let uu____4245 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4245 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4244);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4260 =
                       (is_impure lc1) &&
                         (let uu____4261 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4261) in
                     if uu____4260
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4266 = encode_binders None bs1 env in
                        match uu____4266 with
                        | (vars,guards,envbody,decls,uu____4281) ->
                            let uu____4288 =
                              let uu____4296 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4296
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4288 with
                             | (lc2,body2) ->
                                 let uu____4321 = encode_term body2 envbody in
                                 (match uu____4321 with
                                  | (body3,decls') ->
                                      let uu____4328 =
                                        let uu____4333 = codomain_eff lc2 in
                                        match uu____4333 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4345 =
                                              encode_term tfun env in
                                            (match uu____4345 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4328 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4364 =
                                               let uu____4370 =
                                                 let uu____4371 =
                                                   let uu____4374 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4374, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4371 in
                                               ([], vars, uu____4370) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4364 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4382 =
                                                   let uu____4384 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4384 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4382 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4395 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4395 with
                                            | Some cache_entry ->
                                                let uu____4400 =
                                                  let uu____4401 =
                                                    let uu____4405 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4405) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4401 in
                                                (uu____4400,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4411 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4411 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4418 =
                                                         let uu____4419 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4419 =
                                                           cache_size in
                                                       if uu____4418
                                                       then []
                                                       else
                                                         FStar_List.append
                                                           decls
                                                           (FStar_List.append
                                                              decls' decls'') in
                                                     (t1, decls1)
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         Prims.snd cvars1 in
                                                     let fsym =
                                                       let module_name =
                                                         env.current_module_name in
                                                       let fsym =
                                                         let uu____4430 =
                                                           let uu____4431 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4431 in
                                                         varops.mk_unique
                                                           uu____4430 in
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
                                                       let uu____4436 =
                                                         let uu____4440 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4440) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4436 in
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
                                                           let uu____4452 =
                                                             let uu____4453 =
                                                               let uu____4457
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4457,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4453 in
                                                           [uu____4452] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4465 =
                                                         let uu____4469 =
                                                           let uu____4470 =
                                                             let uu____4476 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4476) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4470 in
                                                         (uu____4469,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4465 in
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
                                                     ((let uu____4486 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4486);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4488,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4489;
                          FStar_Syntax_Syntax.lbunivs = uu____4490;
                          FStar_Syntax_Syntax.lbtyp = uu____4491;
                          FStar_Syntax_Syntax.lbeff = uu____4492;
                          FStar_Syntax_Syntax.lbdef = uu____4493;_}::uu____4494),uu____4495)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4513;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4515;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4531 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4544 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4544, [decl_e])))
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
              let uu____4586 = encode_term e1 env in
              match uu____4586 with
              | (ee1,decls1) ->
                  let uu____4593 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4593 with
                   | (xs,e21) ->
                       let uu____4607 = FStar_List.hd xs in
                       (match uu____4607 with
                        | (x1,uu____4615) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4617 = encode_body e21 env' in
                            (match uu____4617 with
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
            let uu____4639 =
              let uu____4643 =
                let uu____4644 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4644 in
              gen_term_var env uu____4643 in
            match uu____4639 with
            | (scrsym,scr',env1) ->
                let uu____4658 = encode_term e env1 in
                (match uu____4658 with
                 | (scr,decls) ->
                     let uu____4665 =
                       let encode_branch b uu____4681 =
                         match uu____4681 with
                         | (else_case,decls1) ->
                             let uu____4692 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4692 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4722  ->
                                       fun uu____4723  ->
                                         match (uu____4722, uu____4723) with
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
                                                       fun uu____4760  ->
                                                         match uu____4760
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4765 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4780 =
                                                     encode_term w1 env2 in
                                                   (match uu____4780 with
                                                    | (w2,decls21) ->
                                                        let uu____4788 =
                                                          let uu____4789 =
                                                            let uu____4792 =
                                                              let uu____4793
                                                                =
                                                                let uu____4796
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4796) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4793 in
                                                            (guard,
                                                              uu____4792) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4789 in
                                                        (uu____4788, decls21)) in
                                             (match uu____4765 with
                                              | (guard1,decls21) ->
                                                  let uu____4804 =
                                                    encode_br br env2 in
                                                  (match uu____4804 with
                                                   | (br1,decls3) ->
                                                       let uu____4812 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4812,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4665 with
                      | (match_tm,decls1) ->
                          let uu____4824 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4824, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4855 -> let uu____4856 = encode_one_pat env pat in [uu____4856]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4868 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4868
       then
         let uu____4869 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4869
       else ());
      (let uu____4871 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4871 with
       | (vars,pat_term) ->
           let uu____4881 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4904  ->
                     fun v1  ->
                       match uu____4904 with
                       | (env1,vars1) ->
                           let uu____4932 = gen_term_var env1 v1 in
                           (match uu____4932 with
                            | (xx,uu____4944,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4881 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4991 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4999 =
                        let uu____5002 = encode_const c in
                        (scrutinee, uu____5002) in
                      FStar_SMTEncoding_Util.mkEq uu____4999
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5021 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5021 with
                        | (uu____5025,uu____5026::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5028 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5049  ->
                                  match uu____5049 with
                                  | (arg,uu____5055) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5065 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5065)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____5084 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5099 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5114 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5136  ->
                                  match uu____5136 with
                                  | (arg,uu____5145) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5155 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5155)) in
                      FStar_All.pipe_right uu____5114 FStar_List.flatten in
                let pat_term1 uu____5171 = encode_term pat_term env1 in
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
      let uu____5178 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5193  ->
                fun uu____5194  ->
                  match (uu____5193, uu____5194) with
                  | ((tms,decls),(t,uu____5214)) ->
                      let uu____5225 = encode_term t env in
                      (match uu____5225 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5178 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5259 = FStar_Syntax_Util.list_elements e in
        match uu____5259 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5277 =
          let uu____5287 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5287 FStar_Syntax_Util.head_and_args in
        match uu____5277 with
        | (head1,args) ->
            let uu____5318 =
              let uu____5326 =
                let uu____5327 = FStar_Syntax_Util.un_uinst head1 in
                uu____5327.FStar_Syntax_Syntax.n in
              (uu____5326, args) in
            (match uu____5318 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5341,uu____5342)::(e,uu____5344)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5375)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5396 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5429 =
            let uu____5439 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5439 FStar_Syntax_Util.head_and_args in
          match uu____5429 with
          | (head1,args) ->
              let uu____5468 =
                let uu____5476 =
                  let uu____5477 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5477.FStar_Syntax_Syntax.n in
                (uu____5476, args) in
              (match uu____5468 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5490)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5510 -> None) in
        match elts with
        | t1::[] ->
            let uu____5528 = smt_pat_or t1 in
            (match uu____5528 with
             | Some e ->
                 let uu____5544 = list_elements1 e in
                 FStar_All.pipe_right uu____5544
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5561 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5561
                           (FStar_List.map one_pat)))
             | uu____5575 ->
                 let uu____5579 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5579])
        | uu____5610 ->
            let uu____5612 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5612] in
      let uu____5643 =
        let uu____5659 =
          let uu____5660 = FStar_Syntax_Subst.compress t in
          uu____5660.FStar_Syntax_Syntax.n in
        match uu____5659 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5690 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5690 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5725;
                        FStar_Syntax_Syntax.effect_name = uu____5726;
                        FStar_Syntax_Syntax.result_typ = uu____5727;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5729)::(post,uu____5731)::(pats,uu____5733)::[];
                        FStar_Syntax_Syntax.flags = uu____5734;_}
                      ->
                      let uu____5766 = lemma_pats pats in
                      (binders1, pre, post, uu____5766)
                  | uu____5785 -> failwith "impos"))
        | uu____5801 -> failwith "Impos" in
      match uu____5643 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5846 = env in
            {
              bindings = (uu___137_5846.bindings);
              depth = (uu___137_5846.depth);
              tcenv = (uu___137_5846.tcenv);
              warn = (uu___137_5846.warn);
              cache = (uu___137_5846.cache);
              nolabels = (uu___137_5846.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5846.encode_non_total_function_typ);
              current_module_name = (uu___137_5846.current_module_name)
            } in
          let uu____5847 = encode_binders None binders env1 in
          (match uu____5847 with
           | (vars,guards,env2,decls,uu____5862) ->
               let uu____5869 =
                 let uu____5876 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5907 =
                             let uu____5912 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____5928  ->
                                       match uu____5928 with
                                       | (t1,uu____5935) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5912 FStar_List.unzip in
                           match uu____5907 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5876 FStar_List.unzip in
               (match uu____5869 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_5985 = env2 in
                      {
                        bindings = (uu___138_5985.bindings);
                        depth = (uu___138_5985.depth);
                        tcenv = (uu___138_5985.tcenv);
                        warn = (uu___138_5985.warn);
                        cache = (uu___138_5985.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_5985.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_5985.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_5985.current_module_name)
                      } in
                    let uu____5986 =
                      let uu____5989 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5989 env3 in
                    (match uu____5986 with
                     | (pre1,decls'') ->
                         let uu____5994 =
                           let uu____5997 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5997 env3 in
                         (match uu____5994 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6004 =
                                let uu____6005 =
                                  let uu____6011 =
                                    let uu____6012 =
                                      let uu____6015 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6015, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6012 in
                                  (pats, vars, uu____6011) in
                                FStar_SMTEncoding_Util.mkForall uu____6005 in
                              (uu____6004, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6028 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6028
        then
          let uu____6029 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6030 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6029 uu____6030
        else () in
      let enc f r l =
        let uu____6057 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6070 = encode_term (Prims.fst x) env in
                 match uu____6070 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6057 with
        | (decls,args) ->
            let uu____6087 =
              let uu___139_6088 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6088.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6088.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6087, decls) in
      let const_op f r uu____6107 = let uu____6110 = f r in (uu____6110, []) in
      let un_op f l =
        let uu____6126 = FStar_List.hd l in FStar_All.pipe_left f uu____6126 in
      let bin_op f uu___111_6139 =
        match uu___111_6139 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6147 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6174 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6183  ->
                 match uu____6183 with
                 | (t,uu____6191) ->
                     let uu____6192 = encode_formula t env in
                     (match uu____6192 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6174 with
        | (decls,phis) ->
            let uu____6209 =
              let uu___140_6210 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6210.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6210.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6209, decls) in
      let eq_op r uu___112_6226 =
        match uu___112_6226 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6286 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6286 r [e1; e2]
        | l ->
            let uu____6306 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6306 r l in
      let mk_imp1 r uu___113_6325 =
        match uu___113_6325 with
        | (lhs,uu____6329)::(rhs,uu____6331)::[] ->
            let uu____6352 = encode_formula rhs env in
            (match uu____6352 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6361) ->
                      (l1, decls1)
                  | uu____6364 ->
                      let uu____6365 = encode_formula lhs env in
                      (match uu____6365 with
                       | (l2,decls2) ->
                           let uu____6372 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6372, (FStar_List.append decls1 decls2)))))
        | uu____6374 -> failwith "impossible" in
      let mk_ite r uu___114_6389 =
        match uu___114_6389 with
        | (guard,uu____6393)::(_then,uu____6395)::(_else,uu____6397)::[] ->
            let uu____6426 = encode_formula guard env in
            (match uu____6426 with
             | (g,decls1) ->
                 let uu____6433 = encode_formula _then env in
                 (match uu____6433 with
                  | (t,decls2) ->
                      let uu____6440 = encode_formula _else env in
                      (match uu____6440 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6449 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6468 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6468 in
      let connectives =
        let uu____6480 =
          let uu____6489 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6489) in
        let uu____6502 =
          let uu____6512 =
            let uu____6521 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6521) in
          let uu____6534 =
            let uu____6544 =
              let uu____6554 =
                let uu____6563 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6563) in
              let uu____6576 =
                let uu____6586 =
                  let uu____6596 =
                    let uu____6605 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6605) in
                  [uu____6596;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6586 in
              uu____6554 :: uu____6576 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6544 in
          uu____6512 :: uu____6534 in
        uu____6480 :: uu____6502 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6767 = encode_formula phi' env in
            (match uu____6767 with
             | (phi2,decls) ->
                 let uu____6774 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6774, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6775 ->
            let uu____6780 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6780 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6809 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6809 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6817;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6819;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6835 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6835 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6867::(x,uu____6869)::(t,uu____6871)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6905 = encode_term x env in
                 (match uu____6905 with
                  | (x1,decls) ->
                      let uu____6912 = encode_term t env in
                      (match uu____6912 with
                       | (t1,decls') ->
                           let uu____6919 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6919, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6923)::(msg,uu____6925)::(phi2,uu____6927)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6961 =
                   let uu____6964 =
                     let uu____6965 = FStar_Syntax_Subst.compress r in
                     uu____6965.FStar_Syntax_Syntax.n in
                   let uu____6968 =
                     let uu____6969 = FStar_Syntax_Subst.compress msg in
                     uu____6969.FStar_Syntax_Syntax.n in
                   (uu____6964, uu____6968) in
                 (match uu____6961 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6976))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6992 -> fallback phi2)
             | uu____6995 when head_redex env head2 ->
                 let uu____7003 = whnf env phi1 in
                 encode_formula uu____7003 env
             | uu____7004 ->
                 let uu____7012 = encode_term phi1 env in
                 (match uu____7012 with
                  | (tt,decls) ->
                      let uu____7019 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7020 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7020.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7020.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7019, decls)))
        | uu____7023 ->
            let uu____7024 = encode_term phi1 env in
            (match uu____7024 with
             | (tt,decls) ->
                 let uu____7031 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7032 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7032.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7032.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7031, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7059 = encode_binders None bs env1 in
        match uu____7059 with
        | (vars,guards,env2,decls,uu____7081) ->
            let uu____7088 =
              let uu____7095 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7118 =
                          let uu____7123 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7137  ->
                                    match uu____7137 with
                                    | (t,uu____7143) ->
                                        encode_term t
                                          (let uu___143_7144 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7144.bindings);
                                             depth = (uu___143_7144.depth);
                                             tcenv = (uu___143_7144.tcenv);
                                             warn = (uu___143_7144.warn);
                                             cache = (uu___143_7144.cache);
                                             nolabels =
                                               (uu___143_7144.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7144.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7144.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7123 FStar_List.unzip in
                        match uu____7118 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7095 FStar_List.unzip in
            (match uu____7088 with
             | (pats,decls') ->
                 let uu____7196 = encode_formula body env2 in
                 (match uu____7196 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7215;
                             FStar_SMTEncoding_Term.rng = uu____7216;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7224 -> guards in
                      let uu____7227 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7227, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7261  ->
                   match uu____7261 with
                   | (x,uu____7265) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7271 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7277 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7277) uu____7271 tl1 in
             let uu____7279 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7291  ->
                       match uu____7291 with
                       | (b,uu____7295) ->
                           let uu____7296 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7296)) in
             (match uu____7279 with
              | None  -> ()
              | Some (x,uu____7300) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7310 =
                    let uu____7311 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7311 in
                  FStar_Errors.warn pos uu____7310) in
       let uu____7312 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7312 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7318 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7354  ->
                     match uu____7354 with
                     | (l,uu____7364) -> FStar_Ident.lid_equals op l)) in
           (match uu____7318 with
            | None  -> fallback phi1
            | Some (uu____7387,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7416 = encode_q_body env vars pats body in
             match uu____7416 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7442 =
                     let uu____7448 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7448) in
                   FStar_SMTEncoding_Term.mkForall uu____7442
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7460 = encode_q_body env vars pats body in
             match uu____7460 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7485 =
                   let uu____7486 =
                     let uu____7492 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7492) in
                   FStar_SMTEncoding_Term.mkExists uu____7486
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7485, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7541 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7541 with
  | (asym,a) ->
      let uu____7546 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7546 with
       | (xsym,x) ->
           let uu____7551 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7551 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7581 =
                      let uu____7587 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7587, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7581 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7602 =
                      let uu____7606 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7606) in
                    FStar_SMTEncoding_Util.mkApp uu____7602 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7614 =
                    let uu____7616 =
                      let uu____7618 =
                        let uu____7620 =
                          let uu____7621 =
                            let uu____7625 =
                              let uu____7626 =
                                let uu____7632 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7632) in
                              FStar_SMTEncoding_Util.mkForall uu____7626 in
                            (uu____7625, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7621 in
                        let uu____7641 =
                          let uu____7643 =
                            let uu____7644 =
                              let uu____7648 =
                                let uu____7649 =
                                  let uu____7655 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7655) in
                                FStar_SMTEncoding_Util.mkForall uu____7649 in
                              (uu____7648,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7644 in
                          [uu____7643] in
                        uu____7620 :: uu____7641 in
                      xtok_decl :: uu____7618 in
                    xname_decl :: uu____7616 in
                  (xtok1, uu____7614) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7704 =
                    let uu____7712 =
                      let uu____7718 =
                        let uu____7719 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7719 in
                      quant axy uu____7718 in
                    (FStar_Syntax_Const.op_Eq, uu____7712) in
                  let uu____7725 =
                    let uu____7734 =
                      let uu____7742 =
                        let uu____7748 =
                          let uu____7749 =
                            let uu____7750 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7750 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7749 in
                        quant axy uu____7748 in
                      (FStar_Syntax_Const.op_notEq, uu____7742) in
                    let uu____7756 =
                      let uu____7765 =
                        let uu____7773 =
                          let uu____7779 =
                            let uu____7780 =
                              let uu____7781 =
                                let uu____7784 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7785 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7784, uu____7785) in
                              FStar_SMTEncoding_Util.mkLT uu____7781 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7780 in
                          quant xy uu____7779 in
                        (FStar_Syntax_Const.op_LT, uu____7773) in
                      let uu____7791 =
                        let uu____7800 =
                          let uu____7808 =
                            let uu____7814 =
                              let uu____7815 =
                                let uu____7816 =
                                  let uu____7819 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7820 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7819, uu____7820) in
                                FStar_SMTEncoding_Util.mkLTE uu____7816 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7815 in
                            quant xy uu____7814 in
                          (FStar_Syntax_Const.op_LTE, uu____7808) in
                        let uu____7826 =
                          let uu____7835 =
                            let uu____7843 =
                              let uu____7849 =
                                let uu____7850 =
                                  let uu____7851 =
                                    let uu____7854 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7855 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7854, uu____7855) in
                                  FStar_SMTEncoding_Util.mkGT uu____7851 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7850 in
                              quant xy uu____7849 in
                            (FStar_Syntax_Const.op_GT, uu____7843) in
                          let uu____7861 =
                            let uu____7870 =
                              let uu____7878 =
                                let uu____7884 =
                                  let uu____7885 =
                                    let uu____7886 =
                                      let uu____7889 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7890 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7889, uu____7890) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7886 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7885 in
                                quant xy uu____7884 in
                              (FStar_Syntax_Const.op_GTE, uu____7878) in
                            let uu____7896 =
                              let uu____7905 =
                                let uu____7913 =
                                  let uu____7919 =
                                    let uu____7920 =
                                      let uu____7921 =
                                        let uu____7924 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7925 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7924, uu____7925) in
                                      FStar_SMTEncoding_Util.mkSub uu____7921 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7920 in
                                  quant xy uu____7919 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7913) in
                              let uu____7931 =
                                let uu____7940 =
                                  let uu____7948 =
                                    let uu____7954 =
                                      let uu____7955 =
                                        let uu____7956 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7956 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7955 in
                                    quant qx uu____7954 in
                                  (FStar_Syntax_Const.op_Minus, uu____7948) in
                                let uu____7962 =
                                  let uu____7971 =
                                    let uu____7979 =
                                      let uu____7985 =
                                        let uu____7986 =
                                          let uu____7987 =
                                            let uu____7990 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7991 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7990, uu____7991) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7987 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7986 in
                                      quant xy uu____7985 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7979) in
                                  let uu____7997 =
                                    let uu____8006 =
                                      let uu____8014 =
                                        let uu____8020 =
                                          let uu____8021 =
                                            let uu____8022 =
                                              let uu____8025 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8026 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8025, uu____8026) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8022 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8021 in
                                        quant xy uu____8020 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8014) in
                                    let uu____8032 =
                                      let uu____8041 =
                                        let uu____8049 =
                                          let uu____8055 =
                                            let uu____8056 =
                                              let uu____8057 =
                                                let uu____8060 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8061 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8060, uu____8061) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8057 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8056 in
                                          quant xy uu____8055 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8049) in
                                      let uu____8067 =
                                        let uu____8076 =
                                          let uu____8084 =
                                            let uu____8090 =
                                              let uu____8091 =
                                                let uu____8092 =
                                                  let uu____8095 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8096 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8095, uu____8096) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8092 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8091 in
                                            quant xy uu____8090 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8084) in
                                        let uu____8102 =
                                          let uu____8111 =
                                            let uu____8119 =
                                              let uu____8125 =
                                                let uu____8126 =
                                                  let uu____8127 =
                                                    let uu____8130 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8131 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8130, uu____8131) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8127 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8126 in
                                              quant xy uu____8125 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8119) in
                                          let uu____8137 =
                                            let uu____8146 =
                                              let uu____8154 =
                                                let uu____8160 =
                                                  let uu____8161 =
                                                    let uu____8162 =
                                                      let uu____8165 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8166 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8165,
                                                        uu____8166) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8162 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8161 in
                                                quant xy uu____8160 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8154) in
                                            let uu____8172 =
                                              let uu____8181 =
                                                let uu____8189 =
                                                  let uu____8195 =
                                                    let uu____8196 =
                                                      let uu____8197 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8197 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8196 in
                                                  quant qx uu____8195 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8189) in
                                              [uu____8181] in
                                            uu____8146 :: uu____8172 in
                                          uu____8111 :: uu____8137 in
                                        uu____8076 :: uu____8102 in
                                      uu____8041 :: uu____8067 in
                                    uu____8006 :: uu____8032 in
                                  uu____7971 :: uu____7997 in
                                uu____7940 :: uu____7962 in
                              uu____7905 :: uu____7931 in
                            uu____7870 :: uu____7896 in
                          uu____7835 :: uu____7861 in
                        uu____7800 :: uu____7826 in
                      uu____7765 :: uu____7791 in
                    uu____7734 :: uu____7756 in
                  uu____7704 :: uu____7725 in
                let mk1 l v1 =
                  let uu____8325 =
                    let uu____8330 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8362  ->
                              match uu____8362 with
                              | (l',uu____8371) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8330
                      (FStar_Option.map
                         (fun uu____8404  ->
                            match uu____8404 with | (uu____8415,b) -> b v1)) in
                  FStar_All.pipe_right uu____8325 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8456  ->
                          match uu____8456 with
                          | (l',uu____8465) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8491 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8491 with
        | (xxsym,xx) ->
            let uu____8496 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8496 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8504 =
                   let uu____8508 =
                     let uu____8509 =
                       let uu____8515 =
                         let uu____8516 =
                           let uu____8519 =
                             let uu____8520 =
                               let uu____8523 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8523) in
                             FStar_SMTEncoding_Util.mkEq uu____8520 in
                           (xx_has_type, uu____8519) in
                         FStar_SMTEncoding_Util.mkImp uu____8516 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8515) in
                     FStar_SMTEncoding_Util.mkForall uu____8509 in
                   let uu____8536 =
                     let uu____8537 =
                       let uu____8538 =
                         let uu____8539 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8539 in
                       Prims.strcat module_name uu____8538 in
                     varops.mk_unique uu____8537 in
                   (uu____8508, (Some "pretyping"), uu____8536) in
                 FStar_SMTEncoding_Util.mkAssume uu____8504)
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
    let uu____8569 =
      let uu____8570 =
        let uu____8574 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8574, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8570 in
    let uu____8576 =
      let uu____8578 =
        let uu____8579 =
          let uu____8583 =
            let uu____8584 =
              let uu____8590 =
                let uu____8591 =
                  let uu____8594 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8594) in
                FStar_SMTEncoding_Util.mkImp uu____8591 in
              ([[typing_pred]], [xx], uu____8590) in
            mkForall_fuel uu____8584 in
          (uu____8583, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8579 in
      [uu____8578] in
    uu____8569 :: uu____8576 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8622 =
      let uu____8623 =
        let uu____8627 =
          let uu____8628 =
            let uu____8634 =
              let uu____8637 =
                let uu____8639 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8639] in
              [uu____8637] in
            let uu____8642 =
              let uu____8643 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8643 tt in
            (uu____8634, [bb], uu____8642) in
          FStar_SMTEncoding_Util.mkForall uu____8628 in
        (uu____8627, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8623 in
    let uu____8654 =
      let uu____8656 =
        let uu____8657 =
          let uu____8661 =
            let uu____8662 =
              let uu____8668 =
                let uu____8669 =
                  let uu____8672 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8672) in
                FStar_SMTEncoding_Util.mkImp uu____8669 in
              ([[typing_pred]], [xx], uu____8668) in
            mkForall_fuel uu____8662 in
          (uu____8661, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8657 in
      [uu____8656] in
    uu____8622 :: uu____8654 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8706 =
        let uu____8707 =
          let uu____8711 =
            let uu____8713 =
              let uu____8715 =
                let uu____8717 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8718 =
                  let uu____8720 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8720] in
                uu____8717 :: uu____8718 in
              tt :: uu____8715 in
            tt :: uu____8713 in
          ("Prims.Precedes", uu____8711) in
        FStar_SMTEncoding_Util.mkApp uu____8707 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8706 in
    let precedes_y_x =
      let uu____8723 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8723 in
    let uu____8725 =
      let uu____8726 =
        let uu____8730 =
          let uu____8731 =
            let uu____8737 =
              let uu____8740 =
                let uu____8742 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8742] in
              [uu____8740] in
            let uu____8745 =
              let uu____8746 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8746 tt in
            (uu____8737, [bb], uu____8745) in
          FStar_SMTEncoding_Util.mkForall uu____8731 in
        (uu____8730, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8726 in
    let uu____8757 =
      let uu____8759 =
        let uu____8760 =
          let uu____8764 =
            let uu____8765 =
              let uu____8771 =
                let uu____8772 =
                  let uu____8775 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8775) in
                FStar_SMTEncoding_Util.mkImp uu____8772 in
              ([[typing_pred]], [xx], uu____8771) in
            mkForall_fuel uu____8765 in
          (uu____8764, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8760 in
      let uu____8788 =
        let uu____8790 =
          let uu____8791 =
            let uu____8795 =
              let uu____8796 =
                let uu____8802 =
                  let uu____8803 =
                    let uu____8806 =
                      let uu____8807 =
                        let uu____8809 =
                          let uu____8811 =
                            let uu____8813 =
                              let uu____8814 =
                                let uu____8817 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8818 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8817, uu____8818) in
                              FStar_SMTEncoding_Util.mkGT uu____8814 in
                            let uu____8819 =
                              let uu____8821 =
                                let uu____8822 =
                                  let uu____8825 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8826 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8825, uu____8826) in
                                FStar_SMTEncoding_Util.mkGTE uu____8822 in
                              let uu____8827 =
                                let uu____8829 =
                                  let uu____8830 =
                                    let uu____8833 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8834 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8833, uu____8834) in
                                  FStar_SMTEncoding_Util.mkLT uu____8830 in
                                [uu____8829] in
                              uu____8821 :: uu____8827 in
                            uu____8813 :: uu____8819 in
                          typing_pred_y :: uu____8811 in
                        typing_pred :: uu____8809 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8807 in
                    (uu____8806, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8803 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8802) in
              mkForall_fuel uu____8796 in
            (uu____8795, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8791 in
        [uu____8790] in
      uu____8759 :: uu____8788 in
    uu____8725 :: uu____8757 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8864 =
      let uu____8865 =
        let uu____8869 =
          let uu____8870 =
            let uu____8876 =
              let uu____8879 =
                let uu____8881 = FStar_SMTEncoding_Term.boxString b in
                [uu____8881] in
              [uu____8879] in
            let uu____8884 =
              let uu____8885 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8885 tt in
            (uu____8876, [bb], uu____8884) in
          FStar_SMTEncoding_Util.mkForall uu____8870 in
        (uu____8869, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8865 in
    let uu____8896 =
      let uu____8898 =
        let uu____8899 =
          let uu____8903 =
            let uu____8904 =
              let uu____8910 =
                let uu____8911 =
                  let uu____8914 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8914) in
                FStar_SMTEncoding_Util.mkImp uu____8911 in
              ([[typing_pred]], [xx], uu____8910) in
            mkForall_fuel uu____8904 in
          (uu____8903, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8899 in
      [uu____8898] in
    uu____8864 :: uu____8896 in
  let mk_ref1 env reft_name uu____8936 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8947 =
        let uu____8951 =
          let uu____8953 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8953] in
        (reft_name, uu____8951) in
      FStar_SMTEncoding_Util.mkApp uu____8947 in
    let refb =
      let uu____8956 =
        let uu____8960 =
          let uu____8962 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8962] in
        (reft_name, uu____8960) in
      FStar_SMTEncoding_Util.mkApp uu____8956 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8966 =
      let uu____8967 =
        let uu____8971 =
          let uu____8972 =
            let uu____8978 =
              let uu____8979 =
                let uu____8982 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8982) in
              FStar_SMTEncoding_Util.mkImp uu____8979 in
            ([[typing_pred]], [xx; aa], uu____8978) in
          mkForall_fuel uu____8972 in
        (uu____8971, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8967 in
    [uu____8966] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9022 =
      let uu____9023 =
        let uu____9027 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9027, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9023 in
    [uu____9022] in
  let mk_and_interp env conj uu____9038 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9055 =
      let uu____9056 =
        let uu____9060 =
          let uu____9061 =
            let uu____9067 =
              let uu____9068 =
                let uu____9071 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9071, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9068 in
            ([[l_and_a_b]], [aa; bb], uu____9067) in
          FStar_SMTEncoding_Util.mkForall uu____9061 in
        (uu____9060, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9056 in
    [uu____9055] in
  let mk_or_interp env disj uu____9095 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9112 =
      let uu____9113 =
        let uu____9117 =
          let uu____9118 =
            let uu____9124 =
              let uu____9125 =
                let uu____9128 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9128, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9125 in
            ([[l_or_a_b]], [aa; bb], uu____9124) in
          FStar_SMTEncoding_Util.mkForall uu____9118 in
        (uu____9117, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9113 in
    [uu____9112] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9169 =
      let uu____9170 =
        let uu____9174 =
          let uu____9175 =
            let uu____9181 =
              let uu____9182 =
                let uu____9185 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9185, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9182 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9181) in
          FStar_SMTEncoding_Util.mkForall uu____9175 in
        (uu____9174, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9170 in
    [uu____9169] in
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
    let uu____9232 =
      let uu____9233 =
        let uu____9237 =
          let uu____9238 =
            let uu____9244 =
              let uu____9245 =
                let uu____9248 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9248, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9245 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9244) in
          FStar_SMTEncoding_Util.mkForall uu____9238 in
        (uu____9237, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9233 in
    [uu____9232] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9293 =
      let uu____9294 =
        let uu____9298 =
          let uu____9299 =
            let uu____9305 =
              let uu____9306 =
                let uu____9309 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9309, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9306 in
            ([[l_imp_a_b]], [aa; bb], uu____9305) in
          FStar_SMTEncoding_Util.mkForall uu____9299 in
        (uu____9298, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9294 in
    [uu____9293] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9350 =
      let uu____9351 =
        let uu____9355 =
          let uu____9356 =
            let uu____9362 =
              let uu____9363 =
                let uu____9366 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9366, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9363 in
            ([[l_iff_a_b]], [aa; bb], uu____9362) in
          FStar_SMTEncoding_Util.mkForall uu____9356 in
        (uu____9355, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9351 in
    [uu____9350] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9400 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9400 in
    let uu____9402 =
      let uu____9403 =
        let uu____9407 =
          let uu____9408 =
            let uu____9414 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9414) in
          FStar_SMTEncoding_Util.mkForall uu____9408 in
        (uu____9407, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9403 in
    [uu____9402] in
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
      let uu____9454 =
        let uu____9458 =
          let uu____9460 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9460] in
        ("Valid", uu____9458) in
      FStar_SMTEncoding_Util.mkApp uu____9454 in
    let uu____9462 =
      let uu____9463 =
        let uu____9467 =
          let uu____9468 =
            let uu____9474 =
              let uu____9475 =
                let uu____9478 =
                  let uu____9479 =
                    let uu____9485 =
                      let uu____9488 =
                        let uu____9490 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9490] in
                      [uu____9488] in
                    let uu____9493 =
                      let uu____9494 =
                        let uu____9497 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9497, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9494 in
                    (uu____9485, [xx1], uu____9493) in
                  FStar_SMTEncoding_Util.mkForall uu____9479 in
                (uu____9478, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9475 in
            ([[l_forall_a_b]], [aa; bb], uu____9474) in
          FStar_SMTEncoding_Util.mkForall uu____9468 in
        (uu____9467, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9463 in
    [uu____9462] in
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
      let uu____9548 =
        let uu____9552 =
          let uu____9554 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9554] in
        ("Valid", uu____9552) in
      FStar_SMTEncoding_Util.mkApp uu____9548 in
    let uu____9556 =
      let uu____9557 =
        let uu____9561 =
          let uu____9562 =
            let uu____9568 =
              let uu____9569 =
                let uu____9572 =
                  let uu____9573 =
                    let uu____9579 =
                      let uu____9582 =
                        let uu____9584 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9584] in
                      [uu____9582] in
                    let uu____9587 =
                      let uu____9588 =
                        let uu____9591 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9591, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9588 in
                    (uu____9579, [xx1], uu____9587) in
                  FStar_SMTEncoding_Util.mkExists uu____9573 in
                (uu____9572, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9569 in
            ([[l_exists_a_b]], [aa; bb], uu____9568) in
          FStar_SMTEncoding_Util.mkForall uu____9562 in
        (uu____9561, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9557 in
    [uu____9556] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9627 =
      let uu____9628 =
        let uu____9632 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9633 = varops.mk_unique "typing_range_const" in
        (uu____9632, (Some "Range_const typing"), uu____9633) in
      FStar_SMTEncoding_Util.mkAssume uu____9628 in
    [uu____9627] in
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
          let uu____9895 =
            FStar_Util.find_opt
              (fun uu____9913  ->
                 match uu____9913 with
                 | (l,uu____9923) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9895 with
          | None  -> []
          | Some (uu____9945,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9982 = encode_function_type_as_formula t env in
        match uu____9982 with
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
            let uu____10014 =
              (let uu____10015 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10015) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10014
            then
              let uu____10019 = new_term_constant_and_tok_from_lid env lid in
              match uu____10019 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10031 =
                      let uu____10032 = FStar_Syntax_Subst.compress t_norm in
                      uu____10032.FStar_Syntax_Syntax.n in
                    match uu____10031 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10037) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10054  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10057 -> [] in
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
              (let uu____10066 = prims.is lid in
               if uu____10066
               then
                 let vname = varops.new_fvar lid in
                 let uu____10071 = prims.mk lid vname in
                 match uu____10071 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10086 =
                    let uu____10092 = curried_arrow_formals_comp t_norm in
                    match uu____10092 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10103 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10103
                          then
                            let uu____10104 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10105 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10105.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10105.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10105.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10105.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10105.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10105.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10105.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10105.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10105.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10105.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10105.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10105.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10105.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10105.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10105.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10105.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10105.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10105.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10105.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10105.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10105.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10105.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10105.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10104
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10112 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10112)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10086 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10139 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10139 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10152 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10176  ->
                                     match uu___115_10176 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10179 =
                                           FStar_Util.prefix vars in
                                         (match uu____10179 with
                                          | (uu____10190,(xxsym,uu____10192))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10202 =
                                                let uu____10203 =
                                                  let uu____10207 =
                                                    let uu____10208 =
                                                      let uu____10214 =
                                                        let uu____10215 =
                                                          let uu____10218 =
                                                            let uu____10219 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10219 in
                                                          (vapp, uu____10218) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10215 in
                                                      ([[vapp]], vars,
                                                        uu____10214) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10208 in
                                                  (uu____10207,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10203 in
                                              [uu____10202])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10230 =
                                           FStar_Util.prefix vars in
                                         (match uu____10230 with
                                          | (uu____10241,(xxsym,uu____10243))
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
                                              let uu____10257 =
                                                let uu____10258 =
                                                  let uu____10262 =
                                                    let uu____10263 =
                                                      let uu____10269 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10269) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10263 in
                                                  (uu____10262,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10258 in
                                              [uu____10257])
                                     | uu____10278 -> [])) in
                           let uu____10279 = encode_binders None formals env1 in
                           (match uu____10279 with
                            | (vars,guards,env',decls1,uu____10295) ->
                                let uu____10302 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10307 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10307, decls1)
                                  | Some p ->
                                      let uu____10309 = encode_formula p env' in
                                      (match uu____10309 with
                                       | (g,ds) ->
                                           let uu____10316 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10316,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10302 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10325 =
                                         let uu____10329 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10329) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10325 in
                                     let uu____10334 =
                                       let vname_decl =
                                         let uu____10339 =
                                           let uu____10345 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10350  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10345,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10339 in
                                       let uu____10355 =
                                         let env2 =
                                           let uu___145_10359 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10359.bindings);
                                             depth = (uu___145_10359.depth);
                                             tcenv = (uu___145_10359.tcenv);
                                             warn = (uu___145_10359.warn);
                                             cache = (uu___145_10359.cache);
                                             nolabels =
                                               (uu___145_10359.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10359.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10359.current_module_name)
                                           } in
                                         let uu____10360 =
                                           let uu____10361 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10361 in
                                         if uu____10360
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10355 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10371::uu____10372 ->
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
                                                   let uu____10395 =
                                                     let uu____10401 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10401) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10395 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10415 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10417 =
                                             match formals with
                                             | [] ->
                                                 let uu____10426 =
                                                   let uu____10427 =
                                                     let uu____10429 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10429 in
                                                   push_free_var env1 lid
                                                     vname uu____10427 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10426)
                                             | uu____10432 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10437 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10437 in
                                                 let name_tok_corr =
                                                   let uu____10439 =
                                                     let uu____10443 =
                                                       let uu____10444 =
                                                         let uu____10450 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10450) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10444 in
                                                     (uu____10443,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10439 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10417 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10334 with
                                      | (decls2,env2) ->
                                          let uu____10474 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10479 =
                                              encode_term res_t1 env' in
                                            match uu____10479 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10487 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10487,
                                                  decls) in
                                          (match uu____10474 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10495 =
                                                   let uu____10499 =
                                                     let uu____10500 =
                                                       let uu____10506 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10506) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10500 in
                                                   (uu____10499,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10495 in
                                               let freshness =
                                                 let uu____10515 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10515
                                                 then
                                                   let uu____10518 =
                                                     let uu____10519 =
                                                       let uu____10525 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10531 =
                                                         varops.next_id () in
                                                       (vname, uu____10525,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10531) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10519 in
                                                   let uu____10533 =
                                                     let uu____10535 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10535] in
                                                   uu____10518 :: uu____10533
                                                 else [] in
                                               let g =
                                                 let uu____10539 =
                                                   let uu____10541 =
                                                     let uu____10543 =
                                                       let uu____10545 =
                                                         let uu____10547 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10547 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10545 in
                                                     FStar_List.append decls3
                                                       uu____10543 in
                                                   FStar_List.append decls2
                                                     uu____10541 in
                                                 FStar_List.append decls11
                                                   uu____10539 in
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
          let uu____10569 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10569 with
          | None  ->
              let uu____10592 = encode_free_var env x t t_norm [] in
              (match uu____10592 with
               | (decls,env1) ->
                   let uu____10607 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10607 with
                    | (n1,x',uu____10626) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10638) -> ((n1, x1), [], env)
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
          let uu____10671 = encode_free_var env lid t tt quals in
          match uu____10671 with
          | (decls,env1) ->
              let uu____10682 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10682
              then
                let uu____10686 =
                  let uu____10688 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10688 in
                (uu____10686, env1)
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
             (fun uu____10716  ->
                fun lb  ->
                  match uu____10716 with
                  | (decls,env1) ->
                      let uu____10728 =
                        let uu____10732 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10732
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10728 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10746 = FStar_Syntax_Util.head_and_args t in
    match uu____10746 with
    | (hd1,args) ->
        let uu____10772 =
          let uu____10773 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10773.FStar_Syntax_Syntax.n in
        (match uu____10772 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10777,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10790 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10805  ->
      fun quals  ->
        match uu____10805 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10854 = FStar_Util.first_N nbinders formals in
              match uu____10854 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10894  ->
                         fun uu____10895  ->
                           match (uu____10894, uu____10895) with
                           | ((formal,uu____10905),(binder,uu____10907)) ->
                               let uu____10912 =
                                 let uu____10917 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10917) in
                               FStar_Syntax_Syntax.NT uu____10912) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10922 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10936  ->
                              match uu____10936 with
                              | (x,i) ->
                                  let uu____10943 =
                                    let uu___146_10944 = x in
                                    let uu____10945 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_10944.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_10944.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10945
                                    } in
                                  (uu____10943, i))) in
                    FStar_All.pipe_right uu____10922
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10957 =
                      let uu____10959 =
                        let uu____10960 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10960.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10959 in
                    let uu____10964 =
                      let uu____10965 = FStar_Syntax_Subst.compress body in
                      let uu____10966 =
                        let uu____10967 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10967 in
                      FStar_Syntax_Syntax.extend_app_n uu____10965
                        uu____10966 in
                    uu____10964 uu____10957 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11009 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11009
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11010 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11010.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11010.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11010.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11010.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11010.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11010.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11010.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11010.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11010.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11010.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11010.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11010.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11010.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11010.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11010.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11010.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11010.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11010.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11010.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11010.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11010.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11010.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11010.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11031 = FStar_Syntax_Util.abs_formals e in
                match uu____11031 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11080::uu____11081 ->
                         let uu____11089 =
                           let uu____11090 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11090.FStar_Syntax_Syntax.n in
                         (match uu____11089 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11117 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11117 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11143 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11143
                                   then
                                     let uu____11161 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11161 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11207  ->
                                                   fun uu____11208  ->
                                                     match (uu____11207,
                                                             uu____11208)
                                                     with
                                                     | ((x,uu____11218),
                                                        (b,uu____11220)) ->
                                                         let uu____11225 =
                                                           let uu____11230 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11230) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11225)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11232 =
                                            let uu____11243 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11243) in
                                          (uu____11232, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11278 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11278 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11330) ->
                              let uu____11335 =
                                let uu____11346 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11346 in
                              (uu____11335, true)
                          | uu____11379 when Prims.op_Negation norm1 ->
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
                          | uu____11381 ->
                              let uu____11382 =
                                let uu____11383 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11384 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11383
                                  uu____11384 in
                              failwith uu____11382)
                     | uu____11397 ->
                         let uu____11398 =
                           let uu____11399 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11399.FStar_Syntax_Syntax.n in
                         (match uu____11398 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11426 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11426 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11444 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11444 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11492 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11520 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11520
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11527 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11568  ->
                            fun lb  ->
                              match uu____11568 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11619 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11619
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11622 =
                                      let uu____11630 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11630
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11622 with
                                    | (tok,decl,env2) ->
                                        let uu____11655 =
                                          let uu____11662 =
                                            let uu____11668 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11668, tok) in
                                          uu____11662 :: toks in
                                        (uu____11655, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11527 with
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
                        | uu____11770 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11775 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11775 vars)
                            else
                              (let uu____11777 =
                                 let uu____11781 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11781) in
                               FStar_SMTEncoding_Util.mkApp uu____11777) in
                      let uu____11786 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11788  ->
                                 match uu___116_11788 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11789 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11792 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11792))) in
                      if uu____11786
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11812;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11814;
                                FStar_Syntax_Syntax.lbeff = uu____11815;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11856 =
                                 let uu____11860 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11860 with
                                 | (tcenv',uu____11871,e_t) ->
                                     let uu____11875 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11882 -> failwith "Impossible" in
                                     (match uu____11875 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_11891 = env1 in
                                            {
                                              bindings =
                                                (uu___150_11891.bindings);
                                              depth = (uu___150_11891.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_11891.warn);
                                              cache = (uu___150_11891.cache);
                                              nolabels =
                                                (uu___150_11891.nolabels);
                                              use_zfuel_name =
                                                (uu___150_11891.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_11891.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_11891.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11856 with
                                | (env',e1,t_norm1) ->
                                    let uu____11898 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11898 with
                                     | ((binders,body,uu____11910,uu____11911),curry)
                                         ->
                                         ((let uu____11918 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11918
                                           then
                                             let uu____11919 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11920 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11919 uu____11920
                                           else ());
                                          (let uu____11922 =
                                             encode_binders None binders env' in
                                           match uu____11922 with
                                           | (vars,guards,env'1,binder_decls,uu____11938)
                                               ->
                                               let body1 =
                                                 let uu____11946 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11946
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11949 =
                                                 let uu____11954 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11954
                                                 then
                                                   let uu____11960 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11961 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11960, uu____11961)
                                                 else
                                                   (let uu____11967 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11967)) in
                                               (match uu____11949 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11981 =
                                                        let uu____11985 =
                                                          let uu____11986 =
                                                            let uu____11992 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11992) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11986 in
                                                        let uu____11998 =
                                                          let uu____12000 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12000 in
                                                        (uu____11985,
                                                          uu____11998,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11981 in
                                                    let uu____12002 =
                                                      let uu____12004 =
                                                        let uu____12006 =
                                                          let uu____12008 =
                                                            let uu____12010 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12010 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12008 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12006 in
                                                      FStar_List.append
                                                        decls1 uu____12004 in
                                                    (uu____12002, env1))))))
                           | uu____12013 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12032 = varops.fresh "fuel" in
                             (uu____12032, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12035 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12074  ->
                                     fun uu____12075  ->
                                       match (uu____12074, uu____12075) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12157 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12157 in
                                           let gtok =
                                             let uu____12159 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12159 in
                                           let env3 =
                                             let uu____12161 =
                                               let uu____12163 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12163 in
                                             push_free_var env2 flid gtok
                                               uu____12161 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12035 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12249
                                 t_norm uu____12251 =
                                 match (uu____12249, uu____12251) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12278;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12279;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12296 =
                                       let uu____12300 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12300 with
                                       | (tcenv',uu____12315,e_t) ->
                                           let uu____12319 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12326 ->
                                                 failwith "Impossible" in
                                           (match uu____12319 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12335 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12335.bindings);
                                                    depth =
                                                      (uu___151_12335.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12335.warn);
                                                    cache =
                                                      (uu___151_12335.cache);
                                                    nolabels =
                                                      (uu___151_12335.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12335.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12335.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12335.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12296 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12345 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12345
                                            then
                                              let uu____12346 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12347 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12348 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12346 uu____12347
                                                uu____12348
                                            else ());
                                           (let uu____12350 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12350 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12372 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12372
                                                  then
                                                    let uu____12373 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12374 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12375 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12376 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12373 uu____12374
                                                      uu____12375 uu____12376
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12380 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12380 with
                                                  | (vars,guards,env'1,binder_decls,uu____12398)
                                                      ->
                                                      let decl_g =
                                                        let uu____12406 =
                                                          let uu____12412 =
                                                            let uu____12414 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12414 in
                                                          (g, uu____12412,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12406 in
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
                                                        let uu____12429 =
                                                          let uu____12433 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12433) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12429 in
                                                      let gsapp =
                                                        let uu____12439 =
                                                          let uu____12443 =
                                                            let uu____12445 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12445 ::
                                                              vars_tm in
                                                          (g, uu____12443) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12439 in
                                                      let gmax =
                                                        let uu____12449 =
                                                          let uu____12453 =
                                                            let uu____12455 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12455 ::
                                                              vars_tm in
                                                          (g, uu____12453) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12449 in
                                                      let body1 =
                                                        let uu____12459 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12459
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12461 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12461 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12472
                                                               =
                                                               let uu____12476
                                                                 =
                                                                 let uu____12477
                                                                   =
                                                                   let uu____12485
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
                                                                    uu____12485) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12477 in
                                                               let uu____12496
                                                                 =
                                                                 let uu____12498
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12498 in
                                                               (uu____12476,
                                                                 uu____12496,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12472 in
                                                           let eqn_f =
                                                             let uu____12501
                                                               =
                                                               let uu____12505
                                                                 =
                                                                 let uu____12506
                                                                   =
                                                                   let uu____12512
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12512) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12506 in
                                                               (uu____12505,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12501 in
                                                           let eqn_g' =
                                                             let uu____12520
                                                               =
                                                               let uu____12524
                                                                 =
                                                                 let uu____12525
                                                                   =
                                                                   let uu____12531
                                                                    =
                                                                    let uu____12532
                                                                    =
                                                                    let uu____12535
                                                                    =
                                                                    let uu____12536
                                                                    =
                                                                    let uu____12540
                                                                    =
                                                                    let uu____12542
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12542
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12540) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12536 in
                                                                    (gsapp,
                                                                    uu____12535) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12532 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12531) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12525 in
                                                               (uu____12524,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12520 in
                                                           let uu____12554 =
                                                             let uu____12559
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12559
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12576)
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
                                                                    let uu____12591
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12591
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12594
                                                                    =
                                                                    let uu____12598
                                                                    =
                                                                    let uu____12599
                                                                    =
                                                                    let uu____12605
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12605) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12599 in
                                                                    (uu____12598,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12594 in
                                                                 let uu____12616
                                                                   =
                                                                   let uu____12620
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12620
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12628
                                                                    =
                                                                    let uu____12630
                                                                    =
                                                                    let uu____12631
                                                                    =
                                                                    let uu____12635
                                                                    =
                                                                    let uu____12636
                                                                    =
                                                                    let uu____12642
                                                                    =
                                                                    let uu____12643
                                                                    =
                                                                    let uu____12646
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12646,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12643 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12642) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12636 in
                                                                    (uu____12635,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12631 in
                                                                    [uu____12630] in
                                                                    (d3,
                                                                    uu____12628) in
                                                                 (match uu____12616
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12554
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
                               let uu____12681 =
                                 let uu____12688 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12724  ->
                                      fun uu____12725  ->
                                        match (uu____12724, uu____12725) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12811 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12811 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12688 in
                               (match uu____12681 with
                                | (decls2,eqns,env01) ->
                                    let uu____12851 =
                                      let isDeclFun uu___117_12859 =
                                        match uu___117_12859 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12860 -> true
                                        | uu____12866 -> false in
                                      let uu____12867 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12867
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12851 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12894 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12894
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
        let uu____12927 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12927 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12930 = encode_sigelt' env se in
      match uu____12930 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12940 =
                  let uu____12941 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12941 in
                [uu____12940]
            | uu____12942 ->
                let uu____12943 =
                  let uu____12945 =
                    let uu____12946 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12946 in
                  uu____12945 :: g in
                let uu____12947 =
                  let uu____12949 =
                    let uu____12950 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12950 in
                  [uu____12949] in
                FStar_List.append uu____12943 uu____12947 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12958 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12967 =
            let uu____12968 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12968 Prims.op_Negation in
          if uu____12967
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12988 ->
                   let uu____12989 =
                     let uu____12992 =
                       let uu____12993 =
                         let uu____13008 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13008) in
                       FStar_Syntax_Syntax.Tm_abs uu____12993 in
                     FStar_Syntax_Syntax.mk uu____12992 in
                   uu____12989 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13061 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13061 with
               | (aname,atok,env2) ->
                   let uu____13071 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13071 with
                    | (formals,uu____13081) ->
                        let uu____13088 =
                          let uu____13091 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13091 env2 in
                        (match uu____13088 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13099 =
                                 let uu____13100 =
                                   let uu____13106 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13114  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13106,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13100 in
                               [uu____13099;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13121 =
                               let aux uu____13150 uu____13151 =
                                 match (uu____13150, uu____13151) with
                                 | ((bv,uu____13178),(env3,acc_sorts,acc)) ->
                                     let uu____13199 = gen_term_var env3 bv in
                                     (match uu____13199 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13121 with
                              | (uu____13237,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13251 =
                                      let uu____13255 =
                                        let uu____13256 =
                                          let uu____13262 =
                                            let uu____13263 =
                                              let uu____13266 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13266) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13263 in
                                          ([[app]], xs_sorts, uu____13262) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13256 in
                                      (uu____13255, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13251 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13278 =
                                      let uu____13282 =
                                        let uu____13283 =
                                          let uu____13289 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13289) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13283 in
                                      (uu____13282,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13278 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13299 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13299 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13315,uu____13316)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13317 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13317 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13328,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13333 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13335  ->
                      match uu___118_13335 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13338 -> false)) in
            Prims.op_Negation uu____13333 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13344 = encode_top_level_val env fv t quals in
             match uu____13344 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13356 =
                   let uu____13358 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13358 in
                 (uu____13356, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13363 = encode_formula f env in
          (match uu____13363 with
           | (f1,decls) ->
               let g =
                 let uu____13372 =
                   let uu____13373 =
                     let uu____13377 =
                       let uu____13379 =
                         let uu____13380 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13380 in
                       Some uu____13379 in
                     let uu____13381 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13377, uu____13381) in
                   FStar_SMTEncoding_Util.mkAssume uu____13373 in
                 [uu____13372] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13385,uu____13386) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13392 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13399 =
                       let uu____13404 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13404.FStar_Syntax_Syntax.fv_name in
                     uu____13399.FStar_Syntax_Syntax.v in
                   let uu____13408 =
                     let uu____13409 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13409 in
                   if uu____13408
                   then
                     let val_decl =
                       let uu___152_13424 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13424.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13424.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13424.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13428 = encode_sigelt' env1 val_decl in
                     match uu____13428 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13392 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13445,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13447;
                          FStar_Syntax_Syntax.lbtyp = uu____13448;
                          FStar_Syntax_Syntax.lbeff = uu____13449;
                          FStar_Syntax_Syntax.lbdef = uu____13450;_}::[]),uu____13451,uu____13452)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13466 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13466 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13489 =
                   let uu____13491 =
                     let uu____13492 =
                       let uu____13496 =
                         let uu____13497 =
                           let uu____13503 =
                             let uu____13504 =
                               let uu____13507 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13507) in
                             FStar_SMTEncoding_Util.mkEq uu____13504 in
                           ([[b2t_x]], [xx], uu____13503) in
                         FStar_SMTEncoding_Util.mkForall uu____13497 in
                       (uu____13496, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13492 in
                   [uu____13491] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13489 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13524,uu____13525,uu____13526)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13532  ->
                  match uu___119_13532 with
                  | FStar_Syntax_Syntax.Discriminator uu____13533 -> true
                  | uu____13534 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13536,lids,uu____13538) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13545 =
                     let uu____13546 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13546.FStar_Ident.idText in
                   uu____13545 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13548  ->
                     match uu___120_13548 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13549 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13552,uu____13553)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13563  ->
                  match uu___121_13563 with
                  | FStar_Syntax_Syntax.Projector uu____13564 -> true
                  | uu____13567 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13574 = try_lookup_free_var env l in
          (match uu____13574 with
           | Some uu____13578 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13581 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13581.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13581.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13587,uu____13588) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13600) ->
          let uu____13605 = encode_sigelts env ses in
          (match uu____13605 with
           | (g,env1) ->
               let uu____13615 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13625  ->
                         match uu___122_13625 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13626;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13627;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13628;_}
                             -> false
                         | uu____13630 -> true)) in
               (match uu____13615 with
                | (g',inversions) ->
                    let uu____13639 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13649  ->
                              match uu___123_13649 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13650 ->
                                  true
                              | uu____13656 -> false)) in
                    (match uu____13639 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13667,tps,k,uu____13670,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13680  ->
                    match uu___124_13680 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13681 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13688 = c in
              match uu____13688 with
              | (name,args,uu____13692,uu____13693,uu____13694) ->
                  let uu____13697 =
                    let uu____13698 =
                      let uu____13704 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13711  ->
                                match uu____13711 with
                                | (uu____13715,sort,uu____13717) -> sort)) in
                      (name, uu____13704, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13698 in
                  [uu____13697]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13735 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13738 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13738 FStar_Option.isNone)) in
            if uu____13735
            then []
            else
              (let uu____13755 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13755 with
               | (xxsym,xx) ->
                   let uu____13761 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13772  ->
                             fun l  ->
                               match uu____13772 with
                               | (out,decls) ->
                                   let uu____13784 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13784 with
                                    | (uu____13790,data_t) ->
                                        let uu____13792 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13792 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13821 =
                                                 let uu____13822 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13822.FStar_Syntax_Syntax.n in
                                               match uu____13821 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13830,indices) ->
                                                   indices
                                               | uu____13846 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13858  ->
                                                         match uu____13858
                                                         with
                                                         | (x,uu____13862) ->
                                                             let uu____13863
                                                               =
                                                               let uu____13864
                                                                 =
                                                                 let uu____13868
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13868,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13864 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13863)
                                                    env) in
                                             let uu____13870 =
                                               encode_args indices env1 in
                                             (match uu____13870 with
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
                                                      let uu____13890 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13898
                                                                 =
                                                                 let uu____13901
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13901,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13898)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13890
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13903 =
                                                      let uu____13904 =
                                                        let uu____13907 =
                                                          let uu____13908 =
                                                            let uu____13911 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13911,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13908 in
                                                        (out, uu____13907) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13904 in
                                                    (uu____13903,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13761 with
                    | (data_ax,decls) ->
                        let uu____13919 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13919 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13930 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13930 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13933 =
                                 let uu____13937 =
                                   let uu____13938 =
                                     let uu____13944 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13952 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13944,
                                       uu____13952) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13938 in
                                 let uu____13960 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13937, (Some "inversion axiom"),
                                   uu____13960) in
                               FStar_SMTEncoding_Util.mkAssume uu____13933 in
                             let pattern_guarded_inversion =
                               let uu____13964 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13964
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13972 =
                                   let uu____13973 =
                                     let uu____13977 =
                                       let uu____13978 =
                                         let uu____13984 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13992 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13984, uu____13992) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13978 in
                                     let uu____14000 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13977, (Some "inversion axiom"),
                                       uu____14000) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13973 in
                                 [uu____13972]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14003 =
            let uu____14011 =
              let uu____14012 = FStar_Syntax_Subst.compress k in
              uu____14012.FStar_Syntax_Syntax.n in
            match uu____14011 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14041 -> (tps, k) in
          (match uu____14003 with
           | (formals,res) ->
               let uu____14056 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14056 with
                | (formals1,res1) ->
                    let uu____14063 = encode_binders None formals1 env in
                    (match uu____14063 with
                     | (vars,guards,env',binder_decls,uu____14078) ->
                         let uu____14085 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14085 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14098 =
                                  let uu____14102 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14102) in
                                FStar_SMTEncoding_Util.mkApp uu____14098 in
                              let uu____14107 =
                                let tname_decl =
                                  let uu____14113 =
                                    let uu____14114 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14129  ->
                                              match uu____14129 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14137 = varops.next_id () in
                                    (tname, uu____14114,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14137, false) in
                                  constructor_or_logic_type_decl uu____14113 in
                                let uu____14142 =
                                  match vars with
                                  | [] ->
                                      let uu____14149 =
                                        let uu____14150 =
                                          let uu____14152 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14152 in
                                        push_free_var env1 t tname
                                          uu____14150 in
                                      ([], uu____14149)
                                  | uu____14156 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14162 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14162 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14171 =
                                          let uu____14175 =
                                            let uu____14176 =
                                              let uu____14184 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14184) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14176 in
                                          (uu____14175,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14171 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14142 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14107 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14207 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14207 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14221 =
                                               let uu____14222 =
                                                 let uu____14226 =
                                                   let uu____14227 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14227 in
                                                 (uu____14226,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14222 in
                                             [uu____14221]
                                           else [] in
                                         let uu____14230 =
                                           let uu____14232 =
                                             let uu____14234 =
                                               let uu____14235 =
                                                 let uu____14239 =
                                                   let uu____14240 =
                                                     let uu____14246 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14246) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14240 in
                                                 (uu____14239, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14235 in
                                             [uu____14234] in
                                           FStar_List.append karr uu____14232 in
                                         FStar_List.append decls1 uu____14230 in
                                   let aux =
                                     let uu____14255 =
                                       let uu____14257 =
                                         inversion_axioms tapp vars in
                                       let uu____14259 =
                                         let uu____14261 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14261] in
                                       FStar_List.append uu____14257
                                         uu____14259 in
                                     FStar_List.append kindingAx uu____14255 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14266,uu____14267,uu____14268,uu____14269,uu____14270)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14275,t,uu____14277,n_tps,uu____14279) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14284 = new_term_constant_and_tok_from_lid env d in
          (match uu____14284 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14295 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14295 with
                | (formals,t_res) ->
                    let uu____14317 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14317 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14326 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14326 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14364 =
                                            mk_term_projector_name d x in
                                          (uu____14364,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14366 =
                                  let uu____14376 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14376, true) in
                                FStar_All.pipe_right uu____14366
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
                              let uu____14398 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14398 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14406::uu____14407 ->
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
                                         let uu____14432 =
                                           let uu____14438 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14438) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14432
                                     | uu____14451 -> tok_typing in
                                   let uu____14456 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14456 with
                                    | (vars',guards',env'',decls_formals,uu____14471)
                                        ->
                                        let uu____14478 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14478 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14497 ->
                                                   let uu____14501 =
                                                     let uu____14502 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14502 in
                                                   [uu____14501] in
                                             let encode_elim uu____14509 =
                                               let uu____14510 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14510 with
                                               | (head1,args) ->
                                                   let uu____14539 =
                                                     let uu____14540 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14540.FStar_Syntax_Syntax.n in
                                                   (match uu____14539 with
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
                                                        let uu____14558 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14558
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
                                                                 | uu____14584
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14592
                                                                    =
                                                                    let uu____14593
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14593 in
                                                                    if
                                                                    uu____14592
                                                                    then
                                                                    let uu____14600
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14600]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14602
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14615
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14615
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14637
                                                                    =
                                                                    let uu____14641
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14641 in
                                                                    (match uu____14637
                                                                    with
                                                                    | 
                                                                    (uu____14648,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14654
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14654
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14656
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14656
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
                                                             (match uu____14602
                                                              with
                                                              | (uu____14664,arg_vars,elim_eqns_or_guards,uu____14667)
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
                                                                    let uu____14686
                                                                    =
                                                                    let uu____14690
                                                                    =
                                                                    let uu____14691
                                                                    =
                                                                    let uu____14697
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14703
                                                                    =
                                                                    let uu____14704
                                                                    =
                                                                    let uu____14707
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14707) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14704 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14697,
                                                                    uu____14703) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14691 in
                                                                    (uu____14690,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14686 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14720
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14720,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14722
                                                                    =
                                                                    let uu____14726
                                                                    =
                                                                    let uu____14727
                                                                    =
                                                                    let uu____14733
                                                                    =
                                                                    let uu____14736
                                                                    =
                                                                    let uu____14738
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14738] in
                                                                    [uu____14736] in
                                                                    let uu____14741
                                                                    =
                                                                    let uu____14742
                                                                    =
                                                                    let uu____14745
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14746
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14745,
                                                                    uu____14746) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14742 in
                                                                    (uu____14733,
                                                                    [x],
                                                                    uu____14741) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14727 in
                                                                    let uu____14756
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14726,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14756) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14722
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14761
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
                                                                    (let uu____14776
                                                                    =
                                                                    let uu____14777
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14777
                                                                    dapp1 in
                                                                    [uu____14776]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14761
                                                                    FStar_List.flatten in
                                                                    let uu____14781
                                                                    =
                                                                    let uu____14785
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    let uu____14792
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14798
                                                                    =
                                                                    let uu____14799
                                                                    =
                                                                    let uu____14802
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14802) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14799 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14792,
                                                                    uu____14798) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14786 in
                                                                    (uu____14785,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14781) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14812 ->
                                                        ((let uu____14814 =
                                                            let uu____14815 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14816 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14815
                                                              uu____14816 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14814);
                                                         ([], []))) in
                                             let uu____14819 = encode_elim () in
                                             (match uu____14819 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14831 =
                                                      let uu____14833 =
                                                        let uu____14835 =
                                                          let uu____14837 =
                                                            let uu____14839 =
                                                              let uu____14840
                                                                =
                                                                let uu____14846
                                                                  =
                                                                  let uu____14848
                                                                    =
                                                                    let uu____14849
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14849 in
                                                                  Some
                                                                    uu____14848 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14846) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14840 in
                                                            [uu____14839] in
                                                          let uu____14852 =
                                                            let uu____14854 =
                                                              let uu____14856
                                                                =
                                                                let uu____14858
                                                                  =
                                                                  let uu____14860
                                                                    =
                                                                    let uu____14862
                                                                    =
                                                                    let uu____14864
                                                                    =
                                                                    let uu____14865
                                                                    =
                                                                    let uu____14869
                                                                    =
                                                                    let uu____14870
                                                                    =
                                                                    let uu____14876
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14876) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14870 in
                                                                    (uu____14869,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14865 in
                                                                    let uu____14883
                                                                    =
                                                                    let uu____14885
                                                                    =
                                                                    let uu____14886
                                                                    =
                                                                    let uu____14890
                                                                    =
                                                                    let uu____14891
                                                                    =
                                                                    let uu____14897
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14903
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14897,
                                                                    uu____14903) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14891 in
                                                                    (uu____14890,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14886 in
                                                                    [uu____14885] in
                                                                    uu____14864
                                                                    ::
                                                                    uu____14883 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14862 in
                                                                  FStar_List.append
                                                                    uu____14860
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14858 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14856 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14854 in
                                                          FStar_List.append
                                                            uu____14837
                                                            uu____14852 in
                                                        FStar_List.append
                                                          decls3 uu____14835 in
                                                      FStar_List.append
                                                        decls2 uu____14833 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14831 in
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
           (fun uu____14924  ->
              fun se  ->
                match uu____14924 with
                | (g,env1) ->
                    let uu____14936 = encode_sigelt env1 se in
                    (match uu____14936 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14972 =
        match uu____14972 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14990 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14995 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14995
                   then
                     let uu____14996 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14997 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14998 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14996 uu____14997 uu____14998
                   else ());
                  (let uu____15000 = encode_term t1 env1 in
                   match uu____15000 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15010 =
                         let uu____15014 =
                           let uu____15015 =
                             let uu____15016 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15016
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15015 in
                         new_term_constant_from_string env1 x uu____15014 in
                       (match uu____15010 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15027 = FStar_Options.log_queries () in
                              if uu____15027
                              then
                                let uu____15029 =
                                  let uu____15030 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15031 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15032 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15030 uu____15031 uu____15032 in
                                Some uu____15029
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15043,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15052 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15052 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15071 = encode_sigelt env1 se in
                 (match uu____15071 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15081 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15081 with | (uu____15093,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15138  ->
            match uu____15138 with
            | (l,uu____15145,uu____15146) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15167  ->
            match uu____15167 with
            | (l,uu____15175,uu____15176) ->
                let uu____15181 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15182 =
                  let uu____15184 =
                    let uu____15185 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15185 in
                  [uu____15184] in
                uu____15181 :: uu____15182)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15196 =
      let uu____15198 =
        let uu____15199 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15201 =
          let uu____15202 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15202 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15199;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15201
        } in
      [uu____15198] in
    FStar_ST.write last_env uu____15196
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15212 = FStar_ST.read last_env in
      match uu____15212 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15218 ->
          let uu___154_15220 = e in
          let uu____15221 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15220.bindings);
            depth = (uu___154_15220.depth);
            tcenv;
            warn = (uu___154_15220.warn);
            cache = (uu___154_15220.cache);
            nolabels = (uu___154_15220.nolabels);
            use_zfuel_name = (uu___154_15220.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15220.encode_non_total_function_typ);
            current_module_name = uu____15221
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15225 = FStar_ST.read last_env in
    match uu____15225 with
    | [] -> failwith "Empty env stack"
    | uu____15230::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15238  ->
    let uu____15239 = FStar_ST.read last_env in
    match uu____15239 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15250 = hd1 in
          {
            bindings = (uu___155_15250.bindings);
            depth = (uu___155_15250.depth);
            tcenv = (uu___155_15250.tcenv);
            warn = (uu___155_15250.warn);
            cache = refs;
            nolabels = (uu___155_15250.nolabels);
            use_zfuel_name = (uu___155_15250.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15250.encode_non_total_function_typ);
            current_module_name = (uu___155_15250.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15256  ->
    let uu____15257 = FStar_ST.read last_env in
    match uu____15257 with
    | [] -> failwith "Popping an empty stack"
    | uu____15262::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15270  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15273  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15276  ->
    let uu____15277 = FStar_ST.read last_env in
    match uu____15277 with
    | hd1::uu____15283::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15289 -> failwith "Impossible"
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
        | (uu____15338::uu____15339,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15343 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15343.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15343.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15343.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15344 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15355 =
        let uu____15357 =
          let uu____15358 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15358 in
        let uu____15359 = open_fact_db_tags env in uu____15357 :: uu____15359 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15355
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
      let uu____15374 = encode_sigelt env se in
      match uu____15374 with
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
        let uu____15399 = FStar_Options.log_queries () in
        if uu____15399
        then
          let uu____15401 =
            let uu____15402 =
              let uu____15403 =
                let uu____15404 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15404 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15403 in
            FStar_SMTEncoding_Term.Caption uu____15402 in
          uu____15401 :: decls
        else decls in
      let env =
        let uu____15411 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15411 tcenv in
      let uu____15412 = encode_top_level_facts env se in
      match uu____15412 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15421 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15421))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15432 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15432
       then
         let uu____15433 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15433
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15454  ->
                 fun se  ->
                   match uu____15454 with
                   | (g,env2) ->
                       let uu____15466 = encode_top_level_facts env2 se in
                       (match uu____15466 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15479 =
         encode_signature
           (let uu___157_15483 = env in
            {
              bindings = (uu___157_15483.bindings);
              depth = (uu___157_15483.depth);
              tcenv = (uu___157_15483.tcenv);
              warn = false;
              cache = (uu___157_15483.cache);
              nolabels = (uu___157_15483.nolabels);
              use_zfuel_name = (uu___157_15483.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15483.encode_non_total_function_typ);
              current_module_name = (uu___157_15483.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15479 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15495 = FStar_Options.log_queries () in
             if uu____15495
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15500 = env1 in
               {
                 bindings = (uu___158_15500.bindings);
                 depth = (uu___158_15500.depth);
                 tcenv = (uu___158_15500.tcenv);
                 warn = true;
                 cache = (uu___158_15500.cache);
                 nolabels = (uu___158_15500.nolabels);
                 use_zfuel_name = (uu___158_15500.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15500.encode_non_total_function_typ);
                 current_module_name = (uu___158_15500.current_module_name)
               });
            (let uu____15502 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15502
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
        (let uu____15537 =
           let uu____15538 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15538.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15537);
        (let env =
           let uu____15540 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15540 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15547 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15568 = aux rest in
                 (match uu____15568 with
                  | (out,rest1) ->
                      let t =
                        let uu____15586 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15586 with
                        | Some uu____15590 ->
                            let uu____15591 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15591
                              x.FStar_Syntax_Syntax.sort
                        | uu____15592 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15595 =
                        let uu____15597 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_15598 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_15598.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_15598.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15597 :: out in
                      (uu____15595, rest1))
             | uu____15601 -> ([], bindings1) in
           let uu____15605 = aux bindings in
           match uu____15605 with
           | (closing,bindings1) ->
               let uu____15619 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15619, bindings1) in
         match uu____15547 with
         | (q1,bindings1) ->
             let uu____15632 =
               let uu____15635 =
                 FStar_List.filter
                   (fun uu___125_15637  ->
                      match uu___125_15637 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15638 ->
                          false
                      | uu____15642 -> true) bindings1 in
               encode_env_bindings env uu____15635 in
             (match uu____15632 with
              | (env_decls,env1) ->
                  ((let uu____15653 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15653
                    then
                      let uu____15654 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15654
                    else ());
                   (let uu____15656 = encode_formula q1 env1 in
                    match uu____15656 with
                    | (phi,qdecls) ->
                        let uu____15668 =
                          let uu____15671 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15671 phi in
                        (match uu____15668 with
                         | (labels,phi1) ->
                             let uu____15681 = encode_labels labels in
                             (match uu____15681 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15702 =
                                      let uu____15706 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15707 =
                                        varops.mk_unique "@query" in
                                      (uu____15706, (Some "query"),
                                        uu____15707) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15702 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15720 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15720 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15722 = encode_formula q env in
       match uu____15722 with
       | (f,uu____15726) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15728) -> true
             | uu____15731 -> false)))