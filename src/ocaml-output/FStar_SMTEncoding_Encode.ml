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
            let unary uu____2501 =
              let uu____2502 = FStar_List.hd arg_tms in
              FStar_SMTEncoding_Term.unboxInt uu____2502 in
            let binary uu____2508 =
              let uu____2509 =
                let uu____2510 = FStar_List.hd arg_tms in
                FStar_SMTEncoding_Term.unboxInt uu____2510 in
              let uu____2511 =
                let uu____2512 =
                  let uu____2513 = FStar_List.tl arg_tms in
                  FStar_List.hd uu____2513 in
                FStar_SMTEncoding_Term.unboxInt uu____2512 in
              (uu____2509, uu____2511) in
            let mk1 arity f uu____2538 =
              let uu____2543 = let uu____2544 = arity () in f uu____2544 in
              FStar_SMTEncoding_Term.boxInt uu____2543 in
            let ops =
              [(FStar_Syntax_Const.op_Addition,
                 (mk1 binary FStar_SMTEncoding_Util.mkAdd));
              (FStar_Syntax_Const.op_Subtraction,
                (mk1 binary FStar_SMTEncoding_Util.mkSub));
              (FStar_Syntax_Const.op_Multiply,
                (mk1 binary FStar_SMTEncoding_Util.mkMul));
              (FStar_Syntax_Const.op_Division,
                (mk1 binary FStar_SMTEncoding_Util.mkDiv));
              (FStar_Syntax_Const.op_Modulus,
                (mk1 binary FStar_SMTEncoding_Util.mkMod));
              (FStar_Syntax_Const.op_Minus,
                (mk1 unary FStar_SMTEncoding_Util.mkMinus))] in
            (match head1.FStar_Syntax_Syntax.n with
             | FStar_Syntax_Syntax.Tm_fvar fv ->
                 let uu____2604 =
                   let uu____2609 =
                     FStar_List.tryFind
                       (fun uu____2619  ->
                          match uu____2619 with
                          | (l,uu____2625) ->
                              FStar_Syntax_Syntax.fv_eq_lid fv l) ops in
                   FStar_All.pipe_right uu____2609 FStar_Util.must in
                 (match uu____2604 with
                  | (uu____2645,op) ->
                      let uu____2651 = op () in (uu____2651, decls))
             | uu____2652 -> failwith "Impossible")
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2661 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2661
       then
         let uu____2662 = FStar_Syntax_Print.tag_of_term t in
         let uu____2663 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2664 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2662 uu____2663
           uu____2664
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2669 =
             let uu____2670 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2671 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2672 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2673 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2670
               uu____2671 uu____2672 uu____2673 in
           failwith uu____2669
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2677 =
             let uu____2678 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2678 in
           failwith uu____2677
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2683) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2713) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2722 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2722, [])
       | FStar_Syntax_Syntax.Tm_type uu____2728 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2731) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2737 = encode_const c in (uu____2737, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2752 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2752 with
            | (binders1,res) ->
                let uu____2759 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2759
                then
                  let uu____2762 = encode_binders None binders1 env in
                  (match uu____2762 with
                   | (vars,guards,env',decls,uu____2777) ->
                       let fsym =
                         let uu____2787 = varops.fresh "f" in
                         (uu____2787, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2790 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2794 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2794.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2794.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2794.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2794.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2794.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2794.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2794.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2794.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2794.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2794.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2794.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2794.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2794.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2794.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2794.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2794.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2794.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2794.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2794.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2794.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2794.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2794.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2794.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2790 with
                        | (pre_opt,res_t) ->
                            let uu____2801 =
                              encode_term_pred None res_t env' app in
                            (match uu____2801 with
                             | (res_pred,decls') ->
                                 let uu____2808 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2815 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2815, [])
                                   | Some pre ->
                                       let uu____2818 =
                                         encode_formula pre env' in
                                       (match uu____2818 with
                                        | (guard,decls0) ->
                                            let uu____2826 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2826, decls0)) in
                                 (match uu____2808 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2834 =
                                          let uu____2840 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2840) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2834 in
                                      let cvars =
                                        let uu____2850 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2850
                                          (FStar_List.filter
                                             (fun uu____2856  ->
                                                match uu____2856 with
                                                | (x,uu____2860) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2871 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2871 with
                                       | Some cache_entry ->
                                           let uu____2876 =
                                             let uu____2877 =
                                               let uu____2881 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2881) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2877 in
                                           (uu____2876,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____2892 =
                                               let uu____2893 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2893 in
                                             varops.mk_unique uu____2892 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2900 =
                                               FStar_Options.log_queries () in
                                             if uu____2900
                                             then
                                               let uu____2902 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2902
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2908 =
                                               let uu____2912 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2912) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2908 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2920 =
                                               let uu____2924 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2924, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2920 in
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
                                             let uu____2937 =
                                               let uu____2941 =
                                                 let uu____2942 =
                                                   let uu____2948 =
                                                     let uu____2949 =
                                                       let uu____2952 =
                                                         let uu____2953 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2953 in
                                                       (f_has_t, uu____2952) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2949 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2948) in
                                                 mkForall_fuel uu____2942 in
                                               (uu____2941,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2937 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2966 =
                                               let uu____2970 =
                                                 let uu____2971 =
                                                   let uu____2977 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2977) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2971 in
                                               (uu____2970, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2966 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2991 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2991);
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
                     let uu____3002 =
                       let uu____3006 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3006, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3002 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3015 =
                       let uu____3019 =
                         let uu____3020 =
                           let uu____3026 =
                             let uu____3027 =
                               let uu____3030 =
                                 let uu____3031 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3031 in
                               (f_has_t, uu____3030) in
                             FStar_SMTEncoding_Util.mkImp uu____3027 in
                           ([[f_has_t]], [fsym], uu____3026) in
                         mkForall_fuel uu____3020 in
                       (uu____3019, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3015 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3045 ->
           let uu____3050 =
             let uu____3053 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3053 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3058;
                 FStar_Syntax_Syntax.pos = uu____3059;
                 FStar_Syntax_Syntax.vars = uu____3060;_} ->
                 let uu____3067 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3067 with
                  | (b,f1) ->
                      let uu____3081 =
                        let uu____3082 = FStar_List.hd b in
                        Prims.fst uu____3082 in
                      (uu____3081, f1))
             | uu____3087 -> failwith "impossible" in
           (match uu____3050 with
            | (x,f) ->
                let uu____3094 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3094 with
                 | (base_t,decls) ->
                     let uu____3101 = gen_term_var env x in
                     (match uu____3101 with
                      | (x1,xtm,env') ->
                          let uu____3110 = encode_formula f env' in
                          (match uu____3110 with
                           | (refinement,decls') ->
                               let uu____3117 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3117 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3128 =
                                        let uu____3130 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3134 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3130
                                          uu____3134 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3128 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3150  ->
                                              match uu____3150 with
                                              | (y,uu____3154) ->
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
                                    let uu____3173 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3173 with
                                     | Some cache_entry ->
                                         let uu____3178 =
                                           let uu____3179 =
                                             let uu____3183 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3183) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3179 in
                                         (uu____3178,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3195 =
                                             let uu____3196 =
                                               let uu____3197 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3197 in
                                             Prims.strcat module_name
                                               uu____3196 in
                                           varops.mk_unique uu____3195 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3206 =
                                             let uu____3210 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3210) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3206 in
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
                                           let uu____3220 =
                                             let uu____3224 =
                                               let uu____3225 =
                                                 let uu____3231 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3231) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3225 in
                                             (uu____3224,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3220 in
                                         let t_kinding =
                                           let uu____3241 =
                                             let uu____3245 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3245,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3241 in
                                         let t_interp =
                                           let uu____3255 =
                                             let uu____3259 =
                                               let uu____3260 =
                                                 let uu____3266 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3266) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3260 in
                                             let uu____3278 =
                                               let uu____3280 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3280 in
                                             (uu____3259, uu____3278,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3255 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3285 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3285);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3302 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3302 in
           let uu____3306 = encode_term_pred None k env ttm in
           (match uu____3306 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3314 =
                    let uu____3318 =
                      let uu____3319 =
                        let uu____3320 =
                          let uu____3321 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3321 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3320 in
                      varops.mk_unique uu____3319 in
                    (t_has_k, (Some "Uvar typing"), uu____3318) in
                  FStar_SMTEncoding_Util.mkAssume uu____3314 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3327 ->
           let uu____3337 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3337 with
            | (head1,args_e) ->
                let uu____3365 =
                  let uu____3373 =
                    let uu____3374 = FStar_Syntax_Subst.compress head1 in
                    uu____3374.FStar_Syntax_Syntax.n in
                  (uu____3373, args_e) in
                (match uu____3365 with
                 | uu____3384 when head_redex env head1 ->
                     let uu____3392 = whnf env t in
                     encode_term uu____3392 env
                 | uu____3393 when is_arithmetic_primitive head1 args_e ->
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
                     let uu____3478 = encode_term v1 env in
                     (match uu____3478 with
                      | (v11,decls1) ->
                          let uu____3485 = encode_term v2 env in
                          (match uu____3485 with
                           | (v21,decls2) ->
                               let uu____3492 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3492,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3494) ->
                     let e0 =
                       let uu____3506 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3506 in
                     ((let uu____3512 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3512
                       then
                         let uu____3513 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3513
                       else ());
                      (let e =
                         let uu____3518 =
                           let uu____3519 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3520 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3519
                             uu____3520 in
                         uu____3518 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3529),(arg,uu____3531)::[]) -> encode_term arg env
                 | uu____3549 ->
                     let uu____3557 = encode_args args_e env in
                     (match uu____3557 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3590 = encode_term head1 env in
                            match uu____3590 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3629 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3629 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3671  ->
                                                 fun uu____3672  ->
                                                   match (uu____3671,
                                                           uu____3672)
                                                   with
                                                   | ((bv,uu____3686),
                                                      (a,uu____3688)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3702 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3702
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3707 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3707 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3717 =
                                                   let uu____3721 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3726 =
                                                     let uu____3727 =
                                                       let uu____3728 =
                                                         let uu____3729 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3729 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3728 in
                                                     varops.mk_unique
                                                       uu____3727 in
                                                   (uu____3721,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3726) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3717 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3746 = lookup_free_var_sym env fv in
                            match uu____3746 with
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
                                let uu____3784 =
                                  let uu____3785 =
                                    let uu____3788 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3788 Prims.fst in
                                  FStar_All.pipe_right uu____3785 Prims.snd in
                                Some uu____3784
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3807,(FStar_Util.Inl t1,uu____3809),uu____3810)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3848,(FStar_Util.Inr c,uu____3850),uu____3851)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3889 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3909 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3909 in
                               let uu____3910 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3910 with
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
                                     | uu____3935 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3980 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3980 with
            | (bs1,body1,opening) ->
                let fallback uu____3995 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____4000 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____4000, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4011 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____4011
                  | FStar_Util.Inr (eff,uu____4013) ->
                      let uu____4019 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____4019 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____4064 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___136_4065 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___136_4065.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___136_4065.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___136_4065.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___136_4065.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___136_4065.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___136_4065.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___136_4065.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___136_4065.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___136_4065.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___136_4065.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___136_4065.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___136_4065.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___136_4065.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___136_4065.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___136_4065.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___136_4065.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___136_4065.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___136_4065.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___136_4065.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___136_4065.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___136_4065.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___136_4065.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___136_4065.FStar_TypeChecker_Env.qname_and_index)
                             }) uu____4064 FStar_Syntax_Syntax.U_unknown in
                        let uu____4066 =
                          let uu____4067 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____4067 in
                        FStar_Util.Inl uu____4066
                    | FStar_Util.Inr (eff_name,uu____4074) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____4105 =
                        let uu____4106 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____4106 in
                      FStar_All.pipe_right uu____4105
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4118 =
                        let uu____4119 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4119 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4127 =
                          let uu____4128 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4128 in
                        FStar_All.pipe_right uu____4127
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4132 =
                             let uu____4133 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4133 in
                           FStar_All.pipe_right uu____4132
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4144 =
                         let uu____4145 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4145 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4144);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____4160 =
                       (is_impure lc1) &&
                         (let uu____4161 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____4161) in
                     if uu____4160
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____4166 = encode_binders None bs1 env in
                        match uu____4166 with
                        | (vars,guards,envbody,decls,uu____4181) ->
                            let uu____4188 =
                              let uu____4196 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____4196
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____4188 with
                             | (lc2,body2) ->
                                 let uu____4221 = encode_term body2 envbody in
                                 (match uu____4221 with
                                  | (body3,decls') ->
                                      let uu____4228 =
                                        let uu____4233 = codomain_eff lc2 in
                                        match uu____4233 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4245 =
                                              encode_term tfun env in
                                            (match uu____4245 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4228 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4264 =
                                               let uu____4270 =
                                                 let uu____4271 =
                                                   let uu____4274 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4274, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4271 in
                                               ([], vars, uu____4270) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4264 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4282 =
                                                   let uu____4284 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4284 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4282 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4295 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4295 with
                                            | Some cache_entry ->
                                                let uu____4300 =
                                                  let uu____4301 =
                                                    let uu____4305 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4305) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4301 in
                                                (uu____4300,
                                                  (FStar_List.append decls
                                                     (FStar_List.append
                                                        decls'
                                                        (FStar_List.append
                                                           decls''
                                                           (use_cache_entry
                                                              cache_entry)))))
                                            | None  ->
                                                let uu____4311 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4311 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4318 =
                                                         let uu____4319 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4319 =
                                                           cache_size in
                                                       if uu____4318
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
                                                         let uu____4330 =
                                                           let uu____4331 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4331 in
                                                         varops.mk_unique
                                                           uu____4330 in
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
                                                       let uu____4336 =
                                                         let uu____4340 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4340) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4336 in
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
                                                           let uu____4352 =
                                                             let uu____4353 =
                                                               let uu____4357
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4357,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4353 in
                                                           [uu____4352] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4365 =
                                                         let uu____4369 =
                                                           let uu____4370 =
                                                             let uu____4376 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4376) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4370 in
                                                         (uu____4369,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4365 in
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
                                                     ((let uu____4386 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4386);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4388,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4389;
                          FStar_Syntax_Syntax.lbunivs = uu____4390;
                          FStar_Syntax_Syntax.lbtyp = uu____4391;
                          FStar_Syntax_Syntax.lbeff = uu____4392;
                          FStar_Syntax_Syntax.lbdef = uu____4393;_}::uu____4394),uu____4395)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4413;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4415;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4431 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4444 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4444, [decl_e])))
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
              let uu____4486 = encode_term e1 env in
              match uu____4486 with
              | (ee1,decls1) ->
                  let uu____4493 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4493 with
                   | (xs,e21) ->
                       let uu____4507 = FStar_List.hd xs in
                       (match uu____4507 with
                        | (x1,uu____4515) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4517 = encode_body e21 env' in
                            (match uu____4517 with
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
            let uu____4539 =
              let uu____4543 =
                let uu____4544 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4544 in
              gen_term_var env uu____4543 in
            match uu____4539 with
            | (scrsym,scr',env1) ->
                let uu____4558 = encode_term e env1 in
                (match uu____4558 with
                 | (scr,decls) ->
                     let uu____4565 =
                       let encode_branch b uu____4581 =
                         match uu____4581 with
                         | (else_case,decls1) ->
                             let uu____4592 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4592 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4622  ->
                                       fun uu____4623  ->
                                         match (uu____4622, uu____4623) with
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
                                                       fun uu____4660  ->
                                                         match uu____4660
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4665 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4680 =
                                                     encode_term w1 env2 in
                                                   (match uu____4680 with
                                                    | (w2,decls21) ->
                                                        let uu____4688 =
                                                          let uu____4689 =
                                                            let uu____4692 =
                                                              let uu____4693
                                                                =
                                                                let uu____4696
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4696) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4693 in
                                                            (guard,
                                                              uu____4692) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4689 in
                                                        (uu____4688, decls21)) in
                                             (match uu____4665 with
                                              | (guard1,decls21) ->
                                                  let uu____4704 =
                                                    encode_br br env2 in
                                                  (match uu____4704 with
                                                   | (br1,decls3) ->
                                                       let uu____4712 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4712,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4565 with
                      | (match_tm,decls1) ->
                          let uu____4724 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4724, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4755 -> let uu____4756 = encode_one_pat env pat in [uu____4756]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4768 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4768
       then
         let uu____4769 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4769
       else ());
      (let uu____4771 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4771 with
       | (vars,pat_term) ->
           let uu____4781 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4804  ->
                     fun v1  ->
                       match uu____4804 with
                       | (env1,vars1) ->
                           let uu____4832 = gen_term_var env1 v1 in
                           (match uu____4832 with
                            | (xx,uu____4844,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4781 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4891 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4899 =
                        let uu____4902 = encode_const c in
                        (scrutinee, uu____4902) in
                      FStar_SMTEncoding_Util.mkEq uu____4899
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4921 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4921 with
                        | (uu____4925,uu____4926::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4928 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4949  ->
                                  match uu____4949 with
                                  | (arg,uu____4955) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4965 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4965)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4984 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4999 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5014 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5036  ->
                                  match uu____5036 with
                                  | (arg,uu____5045) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5055 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5055)) in
                      FStar_All.pipe_right uu____5014 FStar_List.flatten in
                let pat_term1 uu____5071 = encode_term pat_term env1 in
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
      let uu____5078 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5093  ->
                fun uu____5094  ->
                  match (uu____5093, uu____5094) with
                  | ((tms,decls),(t,uu____5114)) ->
                      let uu____5125 = encode_term t env in
                      (match uu____5125 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5078 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5159 = FStar_Syntax_Util.list_elements e in
        match uu____5159 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5177 =
          let uu____5187 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5187 FStar_Syntax_Util.head_and_args in
        match uu____5177 with
        | (head1,args) ->
            let uu____5218 =
              let uu____5226 =
                let uu____5227 = FStar_Syntax_Util.un_uinst head1 in
                uu____5227.FStar_Syntax_Syntax.n in
              (uu____5226, args) in
            (match uu____5218 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5241,uu____5242)::(e,uu____5244)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5275)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5296 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5329 =
            let uu____5339 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5339 FStar_Syntax_Util.head_and_args in
          match uu____5329 with
          | (head1,args) ->
              let uu____5368 =
                let uu____5376 =
                  let uu____5377 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5377.FStar_Syntax_Syntax.n in
                (uu____5376, args) in
              (match uu____5368 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5390)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5410 -> None) in
        match elts with
        | t1::[] ->
            let uu____5428 = smt_pat_or t1 in
            (match uu____5428 with
             | Some e ->
                 let uu____5444 = list_elements1 e in
                 FStar_All.pipe_right uu____5444
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5461 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5461
                           (FStar_List.map one_pat)))
             | uu____5475 ->
                 let uu____5479 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5479])
        | uu____5510 ->
            let uu____5512 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5512] in
      let uu____5543 =
        let uu____5559 =
          let uu____5560 = FStar_Syntax_Subst.compress t in
          uu____5560.FStar_Syntax_Syntax.n in
        match uu____5559 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5590 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5590 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5625;
                        FStar_Syntax_Syntax.effect_name = uu____5626;
                        FStar_Syntax_Syntax.result_typ = uu____5627;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5629)::(post,uu____5631)::(pats,uu____5633)::[];
                        FStar_Syntax_Syntax.flags = uu____5634;_}
                      ->
                      let uu____5666 = lemma_pats pats in
                      (binders1, pre, post, uu____5666)
                  | uu____5685 -> failwith "impos"))
        | uu____5701 -> failwith "Impos" in
      match uu____5543 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5746 = env in
            {
              bindings = (uu___137_5746.bindings);
              depth = (uu___137_5746.depth);
              tcenv = (uu___137_5746.tcenv);
              warn = (uu___137_5746.warn);
              cache = (uu___137_5746.cache);
              nolabels = (uu___137_5746.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5746.encode_non_total_function_typ);
              current_module_name = (uu___137_5746.current_module_name)
            } in
          let uu____5747 = encode_binders None binders env1 in
          (match uu____5747 with
           | (vars,guards,env2,decls,uu____5762) ->
               let uu____5769 =
                 let uu____5776 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5807 =
                             let uu____5812 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____5828  ->
                                       match uu____5828 with
                                       | (t1,uu____5835) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5812 FStar_List.unzip in
                           match uu____5807 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5776 FStar_List.unzip in
               (match uu____5769 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_5885 = env2 in
                      {
                        bindings = (uu___138_5885.bindings);
                        depth = (uu___138_5885.depth);
                        tcenv = (uu___138_5885.tcenv);
                        warn = (uu___138_5885.warn);
                        cache = (uu___138_5885.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_5885.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_5885.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_5885.current_module_name)
                      } in
                    let uu____5886 =
                      let uu____5889 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5889 env3 in
                    (match uu____5886 with
                     | (pre1,decls'') ->
                         let uu____5894 =
                           let uu____5897 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5897 env3 in
                         (match uu____5894 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____5904 =
                                let uu____5905 =
                                  let uu____5911 =
                                    let uu____5912 =
                                      let uu____5915 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____5915, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____5912 in
                                  (pats, vars, uu____5911) in
                                FStar_SMTEncoding_Util.mkForall uu____5905 in
                              (uu____5904, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5928 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5928
        then
          let uu____5929 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5930 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5929 uu____5930
        else () in
      let enc f r l =
        let uu____5957 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5970 = encode_term (Prims.fst x) env in
                 match uu____5970 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5957 with
        | (decls,args) ->
            let uu____5987 =
              let uu___139_5988 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_5988.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_5988.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5987, decls) in
      let const_op f r uu____6007 = let uu____6010 = f r in (uu____6010, []) in
      let un_op f l =
        let uu____6026 = FStar_List.hd l in FStar_All.pipe_left f uu____6026 in
      let bin_op f uu___111_6039 =
        match uu___111_6039 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6047 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6074 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6083  ->
                 match uu____6083 with
                 | (t,uu____6091) ->
                     let uu____6092 = encode_formula t env in
                     (match uu____6092 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6074 with
        | (decls,phis) ->
            let uu____6109 =
              let uu___140_6110 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6110.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6110.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6109, decls) in
      let eq_op r uu___112_6126 =
        match uu___112_6126 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6186 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6186 r [e1; e2]
        | l ->
            let uu____6206 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6206 r l in
      let mk_imp1 r uu___113_6225 =
        match uu___113_6225 with
        | (lhs,uu____6229)::(rhs,uu____6231)::[] ->
            let uu____6252 = encode_formula rhs env in
            (match uu____6252 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6261) ->
                      (l1, decls1)
                  | uu____6264 ->
                      let uu____6265 = encode_formula lhs env in
                      (match uu____6265 with
                       | (l2,decls2) ->
                           let uu____6272 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6272, (FStar_List.append decls1 decls2)))))
        | uu____6274 -> failwith "impossible" in
      let mk_ite r uu___114_6289 =
        match uu___114_6289 with
        | (guard,uu____6293)::(_then,uu____6295)::(_else,uu____6297)::[] ->
            let uu____6326 = encode_formula guard env in
            (match uu____6326 with
             | (g,decls1) ->
                 let uu____6333 = encode_formula _then env in
                 (match uu____6333 with
                  | (t,decls2) ->
                      let uu____6340 = encode_formula _else env in
                      (match uu____6340 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6349 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6368 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6368 in
      let connectives =
        let uu____6380 =
          let uu____6389 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6389) in
        let uu____6402 =
          let uu____6412 =
            let uu____6421 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6421) in
          let uu____6434 =
            let uu____6444 =
              let uu____6454 =
                let uu____6463 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6463) in
              let uu____6476 =
                let uu____6486 =
                  let uu____6496 =
                    let uu____6505 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6505) in
                  [uu____6496;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6486 in
              uu____6454 :: uu____6476 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6444 in
          uu____6412 :: uu____6434 in
        uu____6380 :: uu____6402 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6667 = encode_formula phi' env in
            (match uu____6667 with
             | (phi2,decls) ->
                 let uu____6674 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6674, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6675 ->
            let uu____6680 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6680 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6709 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6709 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6717;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6719;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6735 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6735 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6767::(x,uu____6769)::(t,uu____6771)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6805 = encode_term x env in
                 (match uu____6805 with
                  | (x1,decls) ->
                      let uu____6812 = encode_term t env in
                      (match uu____6812 with
                       | (t1,decls') ->
                           let uu____6819 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6819, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6823)::(msg,uu____6825)::(phi2,uu____6827)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6861 =
                   let uu____6864 =
                     let uu____6865 = FStar_Syntax_Subst.compress r in
                     uu____6865.FStar_Syntax_Syntax.n in
                   let uu____6868 =
                     let uu____6869 = FStar_Syntax_Subst.compress msg in
                     uu____6869.FStar_Syntax_Syntax.n in
                   (uu____6864, uu____6868) in
                 (match uu____6861 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6876))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6892 -> fallback phi2)
             | uu____6895 when head_redex env head2 ->
                 let uu____6903 = whnf env phi1 in
                 encode_formula uu____6903 env
             | uu____6904 ->
                 let uu____6912 = encode_term phi1 env in
                 (match uu____6912 with
                  | (tt,decls) ->
                      let uu____6919 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_6920 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_6920.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_6920.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6919, decls)))
        | uu____6923 ->
            let uu____6924 = encode_term phi1 env in
            (match uu____6924 with
             | (tt,decls) ->
                 let uu____6931 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_6932 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_6932.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_6932.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6931, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6959 = encode_binders None bs env1 in
        match uu____6959 with
        | (vars,guards,env2,decls,uu____6981) ->
            let uu____6988 =
              let uu____6995 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7018 =
                          let uu____7023 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7037  ->
                                    match uu____7037 with
                                    | (t,uu____7043) ->
                                        encode_term t
                                          (let uu___143_7044 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7044.bindings);
                                             depth = (uu___143_7044.depth);
                                             tcenv = (uu___143_7044.tcenv);
                                             warn = (uu___143_7044.warn);
                                             cache = (uu___143_7044.cache);
                                             nolabels =
                                               (uu___143_7044.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7044.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7044.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7023 FStar_List.unzip in
                        match uu____7018 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6995 FStar_List.unzip in
            (match uu____6988 with
             | (pats,decls') ->
                 let uu____7096 = encode_formula body env2 in
                 (match uu____7096 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7115;
                             FStar_SMTEncoding_Term.rng = uu____7116;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7124 -> guards in
                      let uu____7127 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7127, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7161  ->
                   match uu____7161 with
                   | (x,uu____7165) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7171 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7177 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7177) uu____7171 tl1 in
             let uu____7179 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7191  ->
                       match uu____7191 with
                       | (b,uu____7195) ->
                           let uu____7196 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7196)) in
             (match uu____7179 with
              | None  -> ()
              | Some (x,uu____7200) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7210 =
                    let uu____7211 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7211 in
                  FStar_Errors.warn pos uu____7210) in
       let uu____7212 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7212 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7218 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7254  ->
                     match uu____7254 with
                     | (l,uu____7264) -> FStar_Ident.lid_equals op l)) in
           (match uu____7218 with
            | None  -> fallback phi1
            | Some (uu____7287,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7316 = encode_q_body env vars pats body in
             match uu____7316 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7342 =
                     let uu____7348 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7348) in
                   FStar_SMTEncoding_Term.mkForall uu____7342
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7360 = encode_q_body env vars pats body in
             match uu____7360 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7385 =
                   let uu____7386 =
                     let uu____7392 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7392) in
                   FStar_SMTEncoding_Term.mkExists uu____7386
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7385, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7441 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7441 with
  | (asym,a) ->
      let uu____7446 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7446 with
       | (xsym,x) ->
           let uu____7451 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7451 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7481 =
                      let uu____7487 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7487, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7481 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7502 =
                      let uu____7506 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7506) in
                    FStar_SMTEncoding_Util.mkApp uu____7502 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7514 =
                    let uu____7516 =
                      let uu____7518 =
                        let uu____7520 =
                          let uu____7521 =
                            let uu____7525 =
                              let uu____7526 =
                                let uu____7532 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7532) in
                              FStar_SMTEncoding_Util.mkForall uu____7526 in
                            (uu____7525, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7521 in
                        let uu____7541 =
                          let uu____7543 =
                            let uu____7544 =
                              let uu____7548 =
                                let uu____7549 =
                                  let uu____7555 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7555) in
                                FStar_SMTEncoding_Util.mkForall uu____7549 in
                              (uu____7548,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7544 in
                          [uu____7543] in
                        uu____7520 :: uu____7541 in
                      xtok_decl :: uu____7518 in
                    xname_decl :: uu____7516 in
                  (xtok1, uu____7514) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7604 =
                    let uu____7612 =
                      let uu____7618 =
                        let uu____7619 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7619 in
                      quant axy uu____7618 in
                    (FStar_Syntax_Const.op_Eq, uu____7612) in
                  let uu____7625 =
                    let uu____7634 =
                      let uu____7642 =
                        let uu____7648 =
                          let uu____7649 =
                            let uu____7650 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7650 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7649 in
                        quant axy uu____7648 in
                      (FStar_Syntax_Const.op_notEq, uu____7642) in
                    let uu____7656 =
                      let uu____7665 =
                        let uu____7673 =
                          let uu____7679 =
                            let uu____7680 =
                              let uu____7681 =
                                let uu____7684 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7685 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7684, uu____7685) in
                              FStar_SMTEncoding_Util.mkLT uu____7681 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7680 in
                          quant xy uu____7679 in
                        (FStar_Syntax_Const.op_LT, uu____7673) in
                      let uu____7691 =
                        let uu____7700 =
                          let uu____7708 =
                            let uu____7714 =
                              let uu____7715 =
                                let uu____7716 =
                                  let uu____7719 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7720 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7719, uu____7720) in
                                FStar_SMTEncoding_Util.mkLTE uu____7716 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7715 in
                            quant xy uu____7714 in
                          (FStar_Syntax_Const.op_LTE, uu____7708) in
                        let uu____7726 =
                          let uu____7735 =
                            let uu____7743 =
                              let uu____7749 =
                                let uu____7750 =
                                  let uu____7751 =
                                    let uu____7754 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7755 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7754, uu____7755) in
                                  FStar_SMTEncoding_Util.mkGT uu____7751 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7750 in
                              quant xy uu____7749 in
                            (FStar_Syntax_Const.op_GT, uu____7743) in
                          let uu____7761 =
                            let uu____7770 =
                              let uu____7778 =
                                let uu____7784 =
                                  let uu____7785 =
                                    let uu____7786 =
                                      let uu____7789 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7790 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7789, uu____7790) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7786 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7785 in
                                quant xy uu____7784 in
                              (FStar_Syntax_Const.op_GTE, uu____7778) in
                            let uu____7796 =
                              let uu____7805 =
                                let uu____7813 =
                                  let uu____7819 =
                                    let uu____7820 =
                                      let uu____7821 =
                                        let uu____7824 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7825 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7824, uu____7825) in
                                      FStar_SMTEncoding_Util.mkSub uu____7821 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7820 in
                                  quant xy uu____7819 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7813) in
                              let uu____7831 =
                                let uu____7840 =
                                  let uu____7848 =
                                    let uu____7854 =
                                      let uu____7855 =
                                        let uu____7856 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7856 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7855 in
                                    quant qx uu____7854 in
                                  (FStar_Syntax_Const.op_Minus, uu____7848) in
                                let uu____7862 =
                                  let uu____7871 =
                                    let uu____7879 =
                                      let uu____7885 =
                                        let uu____7886 =
                                          let uu____7887 =
                                            let uu____7890 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7891 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7890, uu____7891) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7887 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7886 in
                                      quant xy uu____7885 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7879) in
                                  let uu____7897 =
                                    let uu____7906 =
                                      let uu____7914 =
                                        let uu____7920 =
                                          let uu____7921 =
                                            let uu____7922 =
                                              let uu____7925 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7926 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7925, uu____7926) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7922 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7921 in
                                        quant xy uu____7920 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7914) in
                                    let uu____7932 =
                                      let uu____7941 =
                                        let uu____7949 =
                                          let uu____7955 =
                                            let uu____7956 =
                                              let uu____7957 =
                                                let uu____7960 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7961 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7960, uu____7961) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7957 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7956 in
                                          quant xy uu____7955 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7949) in
                                      let uu____7967 =
                                        let uu____7976 =
                                          let uu____7984 =
                                            let uu____7990 =
                                              let uu____7991 =
                                                let uu____7992 =
                                                  let uu____7995 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7996 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7995, uu____7996) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7992 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7991 in
                                            quant xy uu____7990 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7984) in
                                        let uu____8002 =
                                          let uu____8011 =
                                            let uu____8019 =
                                              let uu____8025 =
                                                let uu____8026 =
                                                  let uu____8027 =
                                                    let uu____8030 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8031 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8030, uu____8031) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8027 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8026 in
                                              quant xy uu____8025 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8019) in
                                          let uu____8037 =
                                            let uu____8046 =
                                              let uu____8054 =
                                                let uu____8060 =
                                                  let uu____8061 =
                                                    let uu____8062 =
                                                      let uu____8065 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8066 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8065,
                                                        uu____8066) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8062 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8061 in
                                                quant xy uu____8060 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8054) in
                                            let uu____8072 =
                                              let uu____8081 =
                                                let uu____8089 =
                                                  let uu____8095 =
                                                    let uu____8096 =
                                                      let uu____8097 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8097 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8096 in
                                                  quant qx uu____8095 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8089) in
                                              [uu____8081] in
                                            uu____8046 :: uu____8072 in
                                          uu____8011 :: uu____8037 in
                                        uu____7976 :: uu____8002 in
                                      uu____7941 :: uu____7967 in
                                    uu____7906 :: uu____7932 in
                                  uu____7871 :: uu____7897 in
                                uu____7840 :: uu____7862 in
                              uu____7805 :: uu____7831 in
                            uu____7770 :: uu____7796 in
                          uu____7735 :: uu____7761 in
                        uu____7700 :: uu____7726 in
                      uu____7665 :: uu____7691 in
                    uu____7634 :: uu____7656 in
                  uu____7604 :: uu____7625 in
                let mk1 l v1 =
                  let uu____8225 =
                    let uu____8230 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8262  ->
                              match uu____8262 with
                              | (l',uu____8271) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8230
                      (FStar_Option.map
                         (fun uu____8304  ->
                            match uu____8304 with | (uu____8315,b) -> b v1)) in
                  FStar_All.pipe_right uu____8225 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8356  ->
                          match uu____8356 with
                          | (l',uu____8365) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8391 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8391 with
        | (xxsym,xx) ->
            let uu____8396 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8396 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8404 =
                   let uu____8408 =
                     let uu____8409 =
                       let uu____8415 =
                         let uu____8416 =
                           let uu____8419 =
                             let uu____8420 =
                               let uu____8423 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8423) in
                             FStar_SMTEncoding_Util.mkEq uu____8420 in
                           (xx_has_type, uu____8419) in
                         FStar_SMTEncoding_Util.mkImp uu____8416 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8415) in
                     FStar_SMTEncoding_Util.mkForall uu____8409 in
                   let uu____8436 =
                     let uu____8437 =
                       let uu____8438 =
                         let uu____8439 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8439 in
                       Prims.strcat module_name uu____8438 in
                     varops.mk_unique uu____8437 in
                   (uu____8408, (Some "pretyping"), uu____8436) in
                 FStar_SMTEncoding_Util.mkAssume uu____8404)
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
    let uu____8469 =
      let uu____8470 =
        let uu____8474 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8474, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8470 in
    let uu____8476 =
      let uu____8478 =
        let uu____8479 =
          let uu____8483 =
            let uu____8484 =
              let uu____8490 =
                let uu____8491 =
                  let uu____8494 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8494) in
                FStar_SMTEncoding_Util.mkImp uu____8491 in
              ([[typing_pred]], [xx], uu____8490) in
            mkForall_fuel uu____8484 in
          (uu____8483, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8479 in
      [uu____8478] in
    uu____8469 :: uu____8476 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8522 =
      let uu____8523 =
        let uu____8527 =
          let uu____8528 =
            let uu____8534 =
              let uu____8537 =
                let uu____8539 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8539] in
              [uu____8537] in
            let uu____8542 =
              let uu____8543 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8543 tt in
            (uu____8534, [bb], uu____8542) in
          FStar_SMTEncoding_Util.mkForall uu____8528 in
        (uu____8527, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8523 in
    let uu____8554 =
      let uu____8556 =
        let uu____8557 =
          let uu____8561 =
            let uu____8562 =
              let uu____8568 =
                let uu____8569 =
                  let uu____8572 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8572) in
                FStar_SMTEncoding_Util.mkImp uu____8569 in
              ([[typing_pred]], [xx], uu____8568) in
            mkForall_fuel uu____8562 in
          (uu____8561, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8557 in
      [uu____8556] in
    uu____8522 :: uu____8554 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8606 =
        let uu____8607 =
          let uu____8611 =
            let uu____8613 =
              let uu____8615 =
                let uu____8617 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8618 =
                  let uu____8620 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8620] in
                uu____8617 :: uu____8618 in
              tt :: uu____8615 in
            tt :: uu____8613 in
          ("Prims.Precedes", uu____8611) in
        FStar_SMTEncoding_Util.mkApp uu____8607 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8606 in
    let precedes_y_x =
      let uu____8623 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8623 in
    let uu____8625 =
      let uu____8626 =
        let uu____8630 =
          let uu____8631 =
            let uu____8637 =
              let uu____8640 =
                let uu____8642 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8642] in
              [uu____8640] in
            let uu____8645 =
              let uu____8646 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8646 tt in
            (uu____8637, [bb], uu____8645) in
          FStar_SMTEncoding_Util.mkForall uu____8631 in
        (uu____8630, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8626 in
    let uu____8657 =
      let uu____8659 =
        let uu____8660 =
          let uu____8664 =
            let uu____8665 =
              let uu____8671 =
                let uu____8672 =
                  let uu____8675 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8675) in
                FStar_SMTEncoding_Util.mkImp uu____8672 in
              ([[typing_pred]], [xx], uu____8671) in
            mkForall_fuel uu____8665 in
          (uu____8664, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8660 in
      let uu____8688 =
        let uu____8690 =
          let uu____8691 =
            let uu____8695 =
              let uu____8696 =
                let uu____8702 =
                  let uu____8703 =
                    let uu____8706 =
                      let uu____8707 =
                        let uu____8709 =
                          let uu____8711 =
                            let uu____8713 =
                              let uu____8714 =
                                let uu____8717 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8718 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8717, uu____8718) in
                              FStar_SMTEncoding_Util.mkGT uu____8714 in
                            let uu____8719 =
                              let uu____8721 =
                                let uu____8722 =
                                  let uu____8725 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8726 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8725, uu____8726) in
                                FStar_SMTEncoding_Util.mkGTE uu____8722 in
                              let uu____8727 =
                                let uu____8729 =
                                  let uu____8730 =
                                    let uu____8733 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8734 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8733, uu____8734) in
                                  FStar_SMTEncoding_Util.mkLT uu____8730 in
                                [uu____8729] in
                              uu____8721 :: uu____8727 in
                            uu____8713 :: uu____8719 in
                          typing_pred_y :: uu____8711 in
                        typing_pred :: uu____8709 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8707 in
                    (uu____8706, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8703 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8702) in
              mkForall_fuel uu____8696 in
            (uu____8695, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8691 in
        [uu____8690] in
      uu____8659 :: uu____8688 in
    uu____8625 :: uu____8657 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8764 =
      let uu____8765 =
        let uu____8769 =
          let uu____8770 =
            let uu____8776 =
              let uu____8779 =
                let uu____8781 = FStar_SMTEncoding_Term.boxString b in
                [uu____8781] in
              [uu____8779] in
            let uu____8784 =
              let uu____8785 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8785 tt in
            (uu____8776, [bb], uu____8784) in
          FStar_SMTEncoding_Util.mkForall uu____8770 in
        (uu____8769, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8765 in
    let uu____8796 =
      let uu____8798 =
        let uu____8799 =
          let uu____8803 =
            let uu____8804 =
              let uu____8810 =
                let uu____8811 =
                  let uu____8814 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8814) in
                FStar_SMTEncoding_Util.mkImp uu____8811 in
              ([[typing_pred]], [xx], uu____8810) in
            mkForall_fuel uu____8804 in
          (uu____8803, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8799 in
      [uu____8798] in
    uu____8764 :: uu____8796 in
  let mk_ref1 env reft_name uu____8836 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8847 =
        let uu____8851 =
          let uu____8853 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8853] in
        (reft_name, uu____8851) in
      FStar_SMTEncoding_Util.mkApp uu____8847 in
    let refb =
      let uu____8856 =
        let uu____8860 =
          let uu____8862 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8862] in
        (reft_name, uu____8860) in
      FStar_SMTEncoding_Util.mkApp uu____8856 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8866 =
      let uu____8867 =
        let uu____8871 =
          let uu____8872 =
            let uu____8878 =
              let uu____8879 =
                let uu____8882 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8882) in
              FStar_SMTEncoding_Util.mkImp uu____8879 in
            ([[typing_pred]], [xx; aa], uu____8878) in
          mkForall_fuel uu____8872 in
        (uu____8871, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8867 in
    [uu____8866] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8922 =
      let uu____8923 =
        let uu____8927 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8927, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8923 in
    [uu____8922] in
  let mk_and_interp env conj uu____8938 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8955 =
      let uu____8956 =
        let uu____8960 =
          let uu____8961 =
            let uu____8967 =
              let uu____8968 =
                let uu____8971 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8971, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8968 in
            ([[l_and_a_b]], [aa; bb], uu____8967) in
          FStar_SMTEncoding_Util.mkForall uu____8961 in
        (uu____8960, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8956 in
    [uu____8955] in
  let mk_or_interp env disj uu____8995 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9012 =
      let uu____9013 =
        let uu____9017 =
          let uu____9018 =
            let uu____9024 =
              let uu____9025 =
                let uu____9028 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9028, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9025 in
            ([[l_or_a_b]], [aa; bb], uu____9024) in
          FStar_SMTEncoding_Util.mkForall uu____9018 in
        (uu____9017, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9013 in
    [uu____9012] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9069 =
      let uu____9070 =
        let uu____9074 =
          let uu____9075 =
            let uu____9081 =
              let uu____9082 =
                let uu____9085 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9085, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9082 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9081) in
          FStar_SMTEncoding_Util.mkForall uu____9075 in
        (uu____9074, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9070 in
    [uu____9069] in
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
    let uu____9132 =
      let uu____9133 =
        let uu____9137 =
          let uu____9138 =
            let uu____9144 =
              let uu____9145 =
                let uu____9148 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9148, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9145 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9144) in
          FStar_SMTEncoding_Util.mkForall uu____9138 in
        (uu____9137, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9133 in
    [uu____9132] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9193 =
      let uu____9194 =
        let uu____9198 =
          let uu____9199 =
            let uu____9205 =
              let uu____9206 =
                let uu____9209 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9209, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9206 in
            ([[l_imp_a_b]], [aa; bb], uu____9205) in
          FStar_SMTEncoding_Util.mkForall uu____9199 in
        (uu____9198, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9194 in
    [uu____9193] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9250 =
      let uu____9251 =
        let uu____9255 =
          let uu____9256 =
            let uu____9262 =
              let uu____9263 =
                let uu____9266 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9266, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9263 in
            ([[l_iff_a_b]], [aa; bb], uu____9262) in
          FStar_SMTEncoding_Util.mkForall uu____9256 in
        (uu____9255, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9251 in
    [uu____9250] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9300 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9300 in
    let uu____9302 =
      let uu____9303 =
        let uu____9307 =
          let uu____9308 =
            let uu____9314 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9314) in
          FStar_SMTEncoding_Util.mkForall uu____9308 in
        (uu____9307, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9303 in
    [uu____9302] in
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
      let uu____9354 =
        let uu____9358 =
          let uu____9360 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9360] in
        ("Valid", uu____9358) in
      FStar_SMTEncoding_Util.mkApp uu____9354 in
    let uu____9362 =
      let uu____9363 =
        let uu____9367 =
          let uu____9368 =
            let uu____9374 =
              let uu____9375 =
                let uu____9378 =
                  let uu____9379 =
                    let uu____9385 =
                      let uu____9388 =
                        let uu____9390 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9390] in
                      [uu____9388] in
                    let uu____9393 =
                      let uu____9394 =
                        let uu____9397 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9397, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9394 in
                    (uu____9385, [xx1], uu____9393) in
                  FStar_SMTEncoding_Util.mkForall uu____9379 in
                (uu____9378, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9375 in
            ([[l_forall_a_b]], [aa; bb], uu____9374) in
          FStar_SMTEncoding_Util.mkForall uu____9368 in
        (uu____9367, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9363 in
    [uu____9362] in
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
      let uu____9448 =
        let uu____9452 =
          let uu____9454 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9454] in
        ("Valid", uu____9452) in
      FStar_SMTEncoding_Util.mkApp uu____9448 in
    let uu____9456 =
      let uu____9457 =
        let uu____9461 =
          let uu____9462 =
            let uu____9468 =
              let uu____9469 =
                let uu____9472 =
                  let uu____9473 =
                    let uu____9479 =
                      let uu____9482 =
                        let uu____9484 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9484] in
                      [uu____9482] in
                    let uu____9487 =
                      let uu____9488 =
                        let uu____9491 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9491, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9488 in
                    (uu____9479, [xx1], uu____9487) in
                  FStar_SMTEncoding_Util.mkExists uu____9473 in
                (uu____9472, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9469 in
            ([[l_exists_a_b]], [aa; bb], uu____9468) in
          FStar_SMTEncoding_Util.mkForall uu____9462 in
        (uu____9461, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9457 in
    [uu____9456] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9527 =
      let uu____9528 =
        let uu____9532 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9533 = varops.mk_unique "typing_range_const" in
        (uu____9532, (Some "Range_const typing"), uu____9533) in
      FStar_SMTEncoding_Util.mkAssume uu____9528 in
    [uu____9527] in
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
          let uu____9795 =
            FStar_Util.find_opt
              (fun uu____9813  ->
                 match uu____9813 with
                 | (l,uu____9823) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9795 with
          | None  -> []
          | Some (uu____9845,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9882 = encode_function_type_as_formula t env in
        match uu____9882 with
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
            let uu____9914 =
              (let uu____9915 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9915) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9914
            then
              let uu____9919 = new_term_constant_and_tok_from_lid env lid in
              match uu____9919 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9931 =
                      let uu____9932 = FStar_Syntax_Subst.compress t_norm in
                      uu____9932.FStar_Syntax_Syntax.n in
                    match uu____9931 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9937) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9954  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9957 -> [] in
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
              (let uu____9966 = prims.is lid in
               if uu____9966
               then
                 let vname = varops.new_fvar lid in
                 let uu____9971 = prims.mk lid vname in
                 match uu____9971 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9986 =
                    let uu____9992 = curried_arrow_formals_comp t_norm in
                    match uu____9992 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10003 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10003
                          then
                            let uu____10004 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10005 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10005.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10005.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10005.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10005.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10005.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10005.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10005.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10005.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10005.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10005.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10005.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10005.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10005.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10005.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10005.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10005.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10005.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10005.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10005.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10005.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10005.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10005.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10005.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10004
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10012 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10012)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9986 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10039 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10039 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10052 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10076  ->
                                     match uu___115_10076 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10079 =
                                           FStar_Util.prefix vars in
                                         (match uu____10079 with
                                          | (uu____10090,(xxsym,uu____10092))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10102 =
                                                let uu____10103 =
                                                  let uu____10107 =
                                                    let uu____10108 =
                                                      let uu____10114 =
                                                        let uu____10115 =
                                                          let uu____10118 =
                                                            let uu____10119 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10119 in
                                                          (vapp, uu____10118) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10115 in
                                                      ([[vapp]], vars,
                                                        uu____10114) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10108 in
                                                  (uu____10107,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10103 in
                                              [uu____10102])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10130 =
                                           FStar_Util.prefix vars in
                                         (match uu____10130 with
                                          | (uu____10141,(xxsym,uu____10143))
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
                                              let uu____10157 =
                                                let uu____10158 =
                                                  let uu____10162 =
                                                    let uu____10163 =
                                                      let uu____10169 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10169) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10163 in
                                                  (uu____10162,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10158 in
                                              [uu____10157])
                                     | uu____10178 -> [])) in
                           let uu____10179 = encode_binders None formals env1 in
                           (match uu____10179 with
                            | (vars,guards,env',decls1,uu____10195) ->
                                let uu____10202 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10207 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10207, decls1)
                                  | Some p ->
                                      let uu____10209 = encode_formula p env' in
                                      (match uu____10209 with
                                       | (g,ds) ->
                                           let uu____10216 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10216,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10202 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10225 =
                                         let uu____10229 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10229) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10225 in
                                     let uu____10234 =
                                       let vname_decl =
                                         let uu____10239 =
                                           let uu____10245 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10250  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10245,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10239 in
                                       let uu____10255 =
                                         let env2 =
                                           let uu___145_10259 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10259.bindings);
                                             depth = (uu___145_10259.depth);
                                             tcenv = (uu___145_10259.tcenv);
                                             warn = (uu___145_10259.warn);
                                             cache = (uu___145_10259.cache);
                                             nolabels =
                                               (uu___145_10259.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10259.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10259.current_module_name)
                                           } in
                                         let uu____10260 =
                                           let uu____10261 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10261 in
                                         if uu____10260
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10255 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10271::uu____10272 ->
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
                                                   let uu____10295 =
                                                     let uu____10301 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10301) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10295 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10315 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10317 =
                                             match formals with
                                             | [] ->
                                                 let uu____10326 =
                                                   let uu____10327 =
                                                     let uu____10329 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10329 in
                                                   push_free_var env1 lid
                                                     vname uu____10327 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10326)
                                             | uu____10332 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10337 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10337 in
                                                 let name_tok_corr =
                                                   let uu____10339 =
                                                     let uu____10343 =
                                                       let uu____10344 =
                                                         let uu____10350 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10350) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10344 in
                                                     (uu____10343,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10339 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10317 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10234 with
                                      | (decls2,env2) ->
                                          let uu____10374 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10379 =
                                              encode_term res_t1 env' in
                                            match uu____10379 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10387 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10387,
                                                  decls) in
                                          (match uu____10374 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10395 =
                                                   let uu____10399 =
                                                     let uu____10400 =
                                                       let uu____10406 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10406) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10400 in
                                                   (uu____10399,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10395 in
                                               let freshness =
                                                 let uu____10415 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10415
                                                 then
                                                   let uu____10418 =
                                                     let uu____10419 =
                                                       let uu____10425 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10431 =
                                                         varops.next_id () in
                                                       (vname, uu____10425,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10431) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10419 in
                                                   let uu____10433 =
                                                     let uu____10435 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10435] in
                                                   uu____10418 :: uu____10433
                                                 else [] in
                                               let g =
                                                 let uu____10439 =
                                                   let uu____10441 =
                                                     let uu____10443 =
                                                       let uu____10445 =
                                                         let uu____10447 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10447 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10445 in
                                                     FStar_List.append decls3
                                                       uu____10443 in
                                                   FStar_List.append decls2
                                                     uu____10441 in
                                                 FStar_List.append decls11
                                                   uu____10439 in
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
          let uu____10469 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10469 with
          | None  ->
              let uu____10492 = encode_free_var env x t t_norm [] in
              (match uu____10492 with
               | (decls,env1) ->
                   let uu____10507 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10507 with
                    | (n1,x',uu____10526) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10538) -> ((n1, x1), [], env)
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
          let uu____10571 = encode_free_var env lid t tt quals in
          match uu____10571 with
          | (decls,env1) ->
              let uu____10582 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10582
              then
                let uu____10586 =
                  let uu____10588 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10588 in
                (uu____10586, env1)
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
             (fun uu____10616  ->
                fun lb  ->
                  match uu____10616 with
                  | (decls,env1) ->
                      let uu____10628 =
                        let uu____10632 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10632
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10628 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10646 = FStar_Syntax_Util.head_and_args t in
    match uu____10646 with
    | (hd1,args) ->
        let uu____10672 =
          let uu____10673 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10673.FStar_Syntax_Syntax.n in
        (match uu____10672 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10677,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10690 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10705  ->
      fun quals  ->
        match uu____10705 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10754 = FStar_Util.first_N nbinders formals in
              match uu____10754 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10794  ->
                         fun uu____10795  ->
                           match (uu____10794, uu____10795) with
                           | ((formal,uu____10805),(binder,uu____10807)) ->
                               let uu____10812 =
                                 let uu____10817 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10817) in
                               FStar_Syntax_Syntax.NT uu____10812) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10822 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10836  ->
                              match uu____10836 with
                              | (x,i) ->
                                  let uu____10843 =
                                    let uu___146_10844 = x in
                                    let uu____10845 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_10844.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_10844.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10845
                                    } in
                                  (uu____10843, i))) in
                    FStar_All.pipe_right uu____10822
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10857 =
                      let uu____10859 =
                        let uu____10860 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10860.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10859 in
                    let uu____10864 =
                      let uu____10865 = FStar_Syntax_Subst.compress body in
                      let uu____10866 =
                        let uu____10867 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10867 in
                      FStar_Syntax_Syntax.extend_app_n uu____10865
                        uu____10866 in
                    uu____10864 uu____10857 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10909 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10909
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_10910 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_10910.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_10910.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_10910.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_10910.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_10910.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_10910.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_10910.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_10910.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_10910.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_10910.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_10910.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_10910.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_10910.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_10910.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_10910.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_10910.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_10910.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_10910.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_10910.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_10910.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_10910.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_10910.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_10910.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10931 = FStar_Syntax_Util.abs_formals e in
                match uu____10931 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10980::uu____10981 ->
                         let uu____10989 =
                           let uu____10990 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10990.FStar_Syntax_Syntax.n in
                         (match uu____10989 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11017 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11017 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11043 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11043
                                   then
                                     let uu____11061 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11061 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11107  ->
                                                   fun uu____11108  ->
                                                     match (uu____11107,
                                                             uu____11108)
                                                     with
                                                     | ((x,uu____11118),
                                                        (b,uu____11120)) ->
                                                         let uu____11125 =
                                                           let uu____11130 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11130) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11125)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11132 =
                                            let uu____11143 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11143) in
                                          (uu____11132, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11178 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11178 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11230) ->
                              let uu____11235 =
                                let uu____11246 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11246 in
                              (uu____11235, true)
                          | uu____11279 when Prims.op_Negation norm1 ->
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
                          | uu____11281 ->
                              let uu____11282 =
                                let uu____11283 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11284 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11283
                                  uu____11284 in
                              failwith uu____11282)
                     | uu____11297 ->
                         let uu____11298 =
                           let uu____11299 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11299.FStar_Syntax_Syntax.n in
                         (match uu____11298 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11326 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11326 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11344 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11344 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11392 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11420 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11420
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11427 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11468  ->
                            fun lb  ->
                              match uu____11468 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11519 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11519
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11522 =
                                      let uu____11530 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11530
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11522 with
                                    | (tok,decl,env2) ->
                                        let uu____11555 =
                                          let uu____11562 =
                                            let uu____11568 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11568, tok) in
                                          uu____11562 :: toks in
                                        (uu____11555, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11427 with
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
                        | uu____11670 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11675 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11675 vars)
                            else
                              (let uu____11677 =
                                 let uu____11681 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11681) in
                               FStar_SMTEncoding_Util.mkApp uu____11677) in
                      let uu____11686 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11688  ->
                                 match uu___116_11688 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11689 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11692 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11692))) in
                      if uu____11686
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11712;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11714;
                                FStar_Syntax_Syntax.lbeff = uu____11715;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11756 =
                                 let uu____11760 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11760 with
                                 | (tcenv',uu____11771,e_t) ->
                                     let uu____11775 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11782 -> failwith "Impossible" in
                                     (match uu____11775 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_11791 = env1 in
                                            {
                                              bindings =
                                                (uu___150_11791.bindings);
                                              depth = (uu___150_11791.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_11791.warn);
                                              cache = (uu___150_11791.cache);
                                              nolabels =
                                                (uu___150_11791.nolabels);
                                              use_zfuel_name =
                                                (uu___150_11791.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_11791.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_11791.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11756 with
                                | (env',e1,t_norm1) ->
                                    let uu____11798 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11798 with
                                     | ((binders,body,uu____11810,uu____11811),curry)
                                         ->
                                         ((let uu____11818 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11818
                                           then
                                             let uu____11819 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11820 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11819 uu____11820
                                           else ());
                                          (let uu____11822 =
                                             encode_binders None binders env' in
                                           match uu____11822 with
                                           | (vars,guards,env'1,binder_decls,uu____11838)
                                               ->
                                               let body1 =
                                                 let uu____11846 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11846
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11849 =
                                                 let uu____11854 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11854
                                                 then
                                                   let uu____11860 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11861 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11860, uu____11861)
                                                 else
                                                   (let uu____11867 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11867)) in
                                               (match uu____11849 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11881 =
                                                        let uu____11885 =
                                                          let uu____11886 =
                                                            let uu____11892 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11892) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11886 in
                                                        let uu____11898 =
                                                          let uu____11900 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11900 in
                                                        (uu____11885,
                                                          uu____11898,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11881 in
                                                    let uu____11902 =
                                                      let uu____11904 =
                                                        let uu____11906 =
                                                          let uu____11908 =
                                                            let uu____11910 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11910 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11908 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11906 in
                                                      FStar_List.append
                                                        decls1 uu____11904 in
                                                    (uu____11902, env1))))))
                           | uu____11913 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11932 = varops.fresh "fuel" in
                             (uu____11932, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11935 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11974  ->
                                     fun uu____11975  ->
                                       match (uu____11974, uu____11975) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12057 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12057 in
                                           let gtok =
                                             let uu____12059 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12059 in
                                           let env3 =
                                             let uu____12061 =
                                               let uu____12063 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12063 in
                                             push_free_var env2 flid gtok
                                               uu____12061 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11935 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12149
                                 t_norm uu____12151 =
                                 match (uu____12149, uu____12151) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12178;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12179;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12196 =
                                       let uu____12200 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12200 with
                                       | (tcenv',uu____12215,e_t) ->
                                           let uu____12219 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12226 ->
                                                 failwith "Impossible" in
                                           (match uu____12219 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12235 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12235.bindings);
                                                    depth =
                                                      (uu___151_12235.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12235.warn);
                                                    cache =
                                                      (uu___151_12235.cache);
                                                    nolabels =
                                                      (uu___151_12235.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12235.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12235.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12235.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12196 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12245 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12245
                                            then
                                              let uu____12246 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12247 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12248 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12246 uu____12247
                                                uu____12248
                                            else ());
                                           (let uu____12250 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12250 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12272 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12272
                                                  then
                                                    let uu____12273 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12274 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12275 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12276 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12273 uu____12274
                                                      uu____12275 uu____12276
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12280 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12280 with
                                                  | (vars,guards,env'1,binder_decls,uu____12298)
                                                      ->
                                                      let decl_g =
                                                        let uu____12306 =
                                                          let uu____12312 =
                                                            let uu____12314 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12314 in
                                                          (g, uu____12312,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12306 in
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
                                                        let uu____12329 =
                                                          let uu____12333 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12333) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12329 in
                                                      let gsapp =
                                                        let uu____12339 =
                                                          let uu____12343 =
                                                            let uu____12345 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12345 ::
                                                              vars_tm in
                                                          (g, uu____12343) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12339 in
                                                      let gmax =
                                                        let uu____12349 =
                                                          let uu____12353 =
                                                            let uu____12355 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12355 ::
                                                              vars_tm in
                                                          (g, uu____12353) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12349 in
                                                      let body1 =
                                                        let uu____12359 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12359
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12361 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12361 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12372
                                                               =
                                                               let uu____12376
                                                                 =
                                                                 let uu____12377
                                                                   =
                                                                   let uu____12385
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
                                                                    uu____12385) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12377 in
                                                               let uu____12396
                                                                 =
                                                                 let uu____12398
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12398 in
                                                               (uu____12376,
                                                                 uu____12396,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12372 in
                                                           let eqn_f =
                                                             let uu____12401
                                                               =
                                                               let uu____12405
                                                                 =
                                                                 let uu____12406
                                                                   =
                                                                   let uu____12412
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12412) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12406 in
                                                               (uu____12405,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12401 in
                                                           let eqn_g' =
                                                             let uu____12420
                                                               =
                                                               let uu____12424
                                                                 =
                                                                 let uu____12425
                                                                   =
                                                                   let uu____12431
                                                                    =
                                                                    let uu____12432
                                                                    =
                                                                    let uu____12435
                                                                    =
                                                                    let uu____12436
                                                                    =
                                                                    let uu____12440
                                                                    =
                                                                    let uu____12442
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12442
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12440) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12436 in
                                                                    (gsapp,
                                                                    uu____12435) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12432 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12431) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12425 in
                                                               (uu____12424,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12420 in
                                                           let uu____12454 =
                                                             let uu____12459
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12459
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12476)
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
                                                                    let uu____12491
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12491
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12494
                                                                    =
                                                                    let uu____12498
                                                                    =
                                                                    let uu____12499
                                                                    =
                                                                    let uu____12505
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12505) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12499 in
                                                                    (uu____12498,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12494 in
                                                                 let uu____12516
                                                                   =
                                                                   let uu____12520
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12520
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12528
                                                                    =
                                                                    let uu____12530
                                                                    =
                                                                    let uu____12531
                                                                    =
                                                                    let uu____12535
                                                                    =
                                                                    let uu____12536
                                                                    =
                                                                    let uu____12542
                                                                    =
                                                                    let uu____12543
                                                                    =
                                                                    let uu____12546
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12546,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12543 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12542) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12536 in
                                                                    (uu____12535,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12531 in
                                                                    [uu____12530] in
                                                                    (d3,
                                                                    uu____12528) in
                                                                 (match uu____12516
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12454
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
                               let uu____12581 =
                                 let uu____12588 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12624  ->
                                      fun uu____12625  ->
                                        match (uu____12624, uu____12625) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12711 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12711 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12588 in
                               (match uu____12581 with
                                | (decls2,eqns,env01) ->
                                    let uu____12751 =
                                      let isDeclFun uu___117_12759 =
                                        match uu___117_12759 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12760 -> true
                                        | uu____12766 -> false in
                                      let uu____12767 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12767
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12751 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12794 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12794
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
        let uu____12827 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12827 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12830 = encode_sigelt' env se in
      match uu____12830 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12840 =
                  let uu____12841 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12841 in
                [uu____12840]
            | uu____12842 ->
                let uu____12843 =
                  let uu____12845 =
                    let uu____12846 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12846 in
                  uu____12845 :: g in
                let uu____12847 =
                  let uu____12849 =
                    let uu____12850 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12850 in
                  [uu____12849] in
                FStar_List.append uu____12843 uu____12847 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12858 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12867 =
            let uu____12868 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12868 Prims.op_Negation in
          if uu____12867
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12888 ->
                   let uu____12889 =
                     let uu____12892 =
                       let uu____12893 =
                         let uu____12908 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12908) in
                       FStar_Syntax_Syntax.Tm_abs uu____12893 in
                     FStar_Syntax_Syntax.mk uu____12892 in
                   uu____12889 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12961 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12961 with
               | (aname,atok,env2) ->
                   let uu____12971 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12971 with
                    | (formals,uu____12981) ->
                        let uu____12988 =
                          let uu____12991 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12991 env2 in
                        (match uu____12988 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12999 =
                                 let uu____13000 =
                                   let uu____13006 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13014  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13006,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13000 in
                               [uu____12999;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13021 =
                               let aux uu____13050 uu____13051 =
                                 match (uu____13050, uu____13051) with
                                 | ((bv,uu____13078),(env3,acc_sorts,acc)) ->
                                     let uu____13099 = gen_term_var env3 bv in
                                     (match uu____13099 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13021 with
                              | (uu____13137,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13151 =
                                      let uu____13155 =
                                        let uu____13156 =
                                          let uu____13162 =
                                            let uu____13163 =
                                              let uu____13166 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13166) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13163 in
                                          ([[app]], xs_sorts, uu____13162) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13156 in
                                      (uu____13155, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13151 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13178 =
                                      let uu____13182 =
                                        let uu____13183 =
                                          let uu____13189 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13189) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13183 in
                                      (uu____13182,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13178 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13199 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13199 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13215,uu____13216)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13217 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13217 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13228,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13233 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13235  ->
                      match uu___118_13235 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13238 -> false)) in
            Prims.op_Negation uu____13233 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13244 = encode_top_level_val env fv t quals in
             match uu____13244 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13256 =
                   let uu____13258 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13258 in
                 (uu____13256, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13263 = encode_formula f env in
          (match uu____13263 with
           | (f1,decls) ->
               let g =
                 let uu____13272 =
                   let uu____13273 =
                     let uu____13277 =
                       let uu____13279 =
                         let uu____13280 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13280 in
                       Some uu____13279 in
                     let uu____13281 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13277, uu____13281) in
                   FStar_SMTEncoding_Util.mkAssume uu____13273 in
                 [uu____13272] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13285,uu____13286) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13292 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13299 =
                       let uu____13304 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13304.FStar_Syntax_Syntax.fv_name in
                     uu____13299.FStar_Syntax_Syntax.v in
                   let uu____13308 =
                     let uu____13309 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13309 in
                   if uu____13308
                   then
                     let val_decl =
                       let uu___152_13324 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13324.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13324.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13324.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13328 = encode_sigelt' env1 val_decl in
                     match uu____13328 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13292 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13345,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13347;
                          FStar_Syntax_Syntax.lbtyp = uu____13348;
                          FStar_Syntax_Syntax.lbeff = uu____13349;
                          FStar_Syntax_Syntax.lbdef = uu____13350;_}::[]),uu____13351,uu____13352)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13366 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13366 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13389 =
                   let uu____13391 =
                     let uu____13392 =
                       let uu____13396 =
                         let uu____13397 =
                           let uu____13403 =
                             let uu____13404 =
                               let uu____13407 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13407) in
                             FStar_SMTEncoding_Util.mkEq uu____13404 in
                           ([[b2t_x]], [xx], uu____13403) in
                         FStar_SMTEncoding_Util.mkForall uu____13397 in
                       (uu____13396, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13392 in
                   [uu____13391] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13389 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13424,uu____13425,uu____13426)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13432  ->
                  match uu___119_13432 with
                  | FStar_Syntax_Syntax.Discriminator uu____13433 -> true
                  | uu____13434 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13436,lids,uu____13438) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13445 =
                     let uu____13446 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13446.FStar_Ident.idText in
                   uu____13445 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13448  ->
                     match uu___120_13448 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13449 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13452,uu____13453)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13463  ->
                  match uu___121_13463 with
                  | FStar_Syntax_Syntax.Projector uu____13464 -> true
                  | uu____13467 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13474 = try_lookup_free_var env l in
          (match uu____13474 with
           | Some uu____13478 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13481 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13481.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13481.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13487,uu____13488) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13500) ->
          let uu____13505 = encode_sigelts env ses in
          (match uu____13505 with
           | (g,env1) ->
               let uu____13515 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13525  ->
                         match uu___122_13525 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13526;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13527;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13528;_}
                             -> false
                         | uu____13530 -> true)) in
               (match uu____13515 with
                | (g',inversions) ->
                    let uu____13539 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13549  ->
                              match uu___123_13549 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13550 ->
                                  true
                              | uu____13556 -> false)) in
                    (match uu____13539 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13567,tps,k,uu____13570,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13580  ->
                    match uu___124_13580 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13581 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13588 = c in
              match uu____13588 with
              | (name,args,uu____13592,uu____13593,uu____13594) ->
                  let uu____13597 =
                    let uu____13598 =
                      let uu____13604 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13611  ->
                                match uu____13611 with
                                | (uu____13615,sort,uu____13617) -> sort)) in
                      (name, uu____13604, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13598 in
                  [uu____13597]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13635 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13638 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13638 FStar_Option.isNone)) in
            if uu____13635
            then []
            else
              (let uu____13655 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13655 with
               | (xxsym,xx) ->
                   let uu____13661 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13672  ->
                             fun l  ->
                               match uu____13672 with
                               | (out,decls) ->
                                   let uu____13684 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13684 with
                                    | (uu____13690,data_t) ->
                                        let uu____13692 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13692 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13721 =
                                                 let uu____13722 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13722.FStar_Syntax_Syntax.n in
                                               match uu____13721 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13730,indices) ->
                                                   indices
                                               | uu____13746 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13758  ->
                                                         match uu____13758
                                                         with
                                                         | (x,uu____13762) ->
                                                             let uu____13763
                                                               =
                                                               let uu____13764
                                                                 =
                                                                 let uu____13768
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13768,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13764 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13763)
                                                    env) in
                                             let uu____13770 =
                                               encode_args indices env1 in
                                             (match uu____13770 with
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
                                                      let uu____13790 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13798
                                                                 =
                                                                 let uu____13801
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13801,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13798)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13790
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13803 =
                                                      let uu____13804 =
                                                        let uu____13807 =
                                                          let uu____13808 =
                                                            let uu____13811 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13811,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13808 in
                                                        (out, uu____13807) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13804 in
                                                    (uu____13803,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13661 with
                    | (data_ax,decls) ->
                        let uu____13819 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13819 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13830 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13830 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13833 =
                                 let uu____13837 =
                                   let uu____13838 =
                                     let uu____13844 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13852 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13844,
                                       uu____13852) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13838 in
                                 let uu____13860 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13837, (Some "inversion axiom"),
                                   uu____13860) in
                               FStar_SMTEncoding_Util.mkAssume uu____13833 in
                             let pattern_guarded_inversion =
                               let uu____13864 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13864
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13872 =
                                   let uu____13873 =
                                     let uu____13877 =
                                       let uu____13878 =
                                         let uu____13884 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13892 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13884, uu____13892) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13878 in
                                     let uu____13900 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13877, (Some "inversion axiom"),
                                       uu____13900) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13873 in
                                 [uu____13872]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13903 =
            let uu____13911 =
              let uu____13912 = FStar_Syntax_Subst.compress k in
              uu____13912.FStar_Syntax_Syntax.n in
            match uu____13911 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13941 -> (tps, k) in
          (match uu____13903 with
           | (formals,res) ->
               let uu____13956 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13956 with
                | (formals1,res1) ->
                    let uu____13963 = encode_binders None formals1 env in
                    (match uu____13963 with
                     | (vars,guards,env',binder_decls,uu____13978) ->
                         let uu____13985 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13985 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13998 =
                                  let uu____14002 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14002) in
                                FStar_SMTEncoding_Util.mkApp uu____13998 in
                              let uu____14007 =
                                let tname_decl =
                                  let uu____14013 =
                                    let uu____14014 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14029  ->
                                              match uu____14029 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14037 = varops.next_id () in
                                    (tname, uu____14014,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14037, false) in
                                  constructor_or_logic_type_decl uu____14013 in
                                let uu____14042 =
                                  match vars with
                                  | [] ->
                                      let uu____14049 =
                                        let uu____14050 =
                                          let uu____14052 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14052 in
                                        push_free_var env1 t tname
                                          uu____14050 in
                                      ([], uu____14049)
                                  | uu____14056 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14062 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14062 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14071 =
                                          let uu____14075 =
                                            let uu____14076 =
                                              let uu____14084 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14084) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14076 in
                                          (uu____14075,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14071 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14042 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14007 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14107 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14107 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14121 =
                                               let uu____14122 =
                                                 let uu____14126 =
                                                   let uu____14127 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14127 in
                                                 (uu____14126,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14122 in
                                             [uu____14121]
                                           else [] in
                                         let uu____14130 =
                                           let uu____14132 =
                                             let uu____14134 =
                                               let uu____14135 =
                                                 let uu____14139 =
                                                   let uu____14140 =
                                                     let uu____14146 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14146) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14140 in
                                                 (uu____14139, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14135 in
                                             [uu____14134] in
                                           FStar_List.append karr uu____14132 in
                                         FStar_List.append decls1 uu____14130 in
                                   let aux =
                                     let uu____14155 =
                                       let uu____14157 =
                                         inversion_axioms tapp vars in
                                       let uu____14159 =
                                         let uu____14161 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14161] in
                                       FStar_List.append uu____14157
                                         uu____14159 in
                                     FStar_List.append kindingAx uu____14155 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14166,uu____14167,uu____14168,uu____14169,uu____14170)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14175,t,uu____14177,n_tps,uu____14179) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14184 = new_term_constant_and_tok_from_lid env d in
          (match uu____14184 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14195 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14195 with
                | (formals,t_res) ->
                    let uu____14217 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14217 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14226 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14226 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14264 =
                                            mk_term_projector_name d x in
                                          (uu____14264,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14266 =
                                  let uu____14276 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14276, true) in
                                FStar_All.pipe_right uu____14266
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
                              let uu____14298 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14298 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14306::uu____14307 ->
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
                                         let uu____14332 =
                                           let uu____14338 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14338) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14332
                                     | uu____14351 -> tok_typing in
                                   let uu____14356 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14356 with
                                    | (vars',guards',env'',decls_formals,uu____14371)
                                        ->
                                        let uu____14378 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14378 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14397 ->
                                                   let uu____14401 =
                                                     let uu____14402 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14402 in
                                                   [uu____14401] in
                                             let encode_elim uu____14409 =
                                               let uu____14410 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14410 with
                                               | (head1,args) ->
                                                   let uu____14439 =
                                                     let uu____14440 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14440.FStar_Syntax_Syntax.n in
                                                   (match uu____14439 with
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
                                                        let uu____14458 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14458
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
                                                                 | uu____14484
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14492
                                                                    =
                                                                    let uu____14493
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14493 in
                                                                    if
                                                                    uu____14492
                                                                    then
                                                                    let uu____14500
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14500]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14502
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14515
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14515
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14537
                                                                    =
                                                                    let uu____14541
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14541 in
                                                                    (match uu____14537
                                                                    with
                                                                    | 
                                                                    (uu____14548,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14554
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14554
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14556
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14556
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
                                                             (match uu____14502
                                                              with
                                                              | (uu____14564,arg_vars,elim_eqns_or_guards,uu____14567)
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
                                                                    let uu____14586
                                                                    =
                                                                    let uu____14590
                                                                    =
                                                                    let uu____14591
                                                                    =
                                                                    let uu____14597
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14603
                                                                    =
                                                                    let uu____14604
                                                                    =
                                                                    let uu____14607
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14607) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14604 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14597,
                                                                    uu____14603) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14591 in
                                                                    (uu____14590,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14586 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14620
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14620,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14622
                                                                    =
                                                                    let uu____14626
                                                                    =
                                                                    let uu____14627
                                                                    =
                                                                    let uu____14633
                                                                    =
                                                                    let uu____14636
                                                                    =
                                                                    let uu____14638
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14638] in
                                                                    [uu____14636] in
                                                                    let uu____14641
                                                                    =
                                                                    let uu____14642
                                                                    =
                                                                    let uu____14645
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14646
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14645,
                                                                    uu____14646) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14642 in
                                                                    (uu____14633,
                                                                    [x],
                                                                    uu____14641) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14627 in
                                                                    let uu____14656
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14626,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14656) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14622
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14661
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
                                                                    (let uu____14676
                                                                    =
                                                                    let uu____14677
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14677
                                                                    dapp1 in
                                                                    [uu____14676]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14661
                                                                    FStar_List.flatten in
                                                                    let uu____14681
                                                                    =
                                                                    let uu____14685
                                                                    =
                                                                    let uu____14686
                                                                    =
                                                                    let uu____14692
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14698
                                                                    =
                                                                    let uu____14699
                                                                    =
                                                                    let uu____14702
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14702) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14699 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14692,
                                                                    uu____14698) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14686 in
                                                                    (uu____14685,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14681) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14712 ->
                                                        ((let uu____14714 =
                                                            let uu____14715 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14716 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14715
                                                              uu____14716 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14714);
                                                         ([], []))) in
                                             let uu____14719 = encode_elim () in
                                             (match uu____14719 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14731 =
                                                      let uu____14733 =
                                                        let uu____14735 =
                                                          let uu____14737 =
                                                            let uu____14739 =
                                                              let uu____14740
                                                                =
                                                                let uu____14746
                                                                  =
                                                                  let uu____14748
                                                                    =
                                                                    let uu____14749
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14749 in
                                                                  Some
                                                                    uu____14748 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14746) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14740 in
                                                            [uu____14739] in
                                                          let uu____14752 =
                                                            let uu____14754 =
                                                              let uu____14756
                                                                =
                                                                let uu____14758
                                                                  =
                                                                  let uu____14760
                                                                    =
                                                                    let uu____14762
                                                                    =
                                                                    let uu____14764
                                                                    =
                                                                    let uu____14765
                                                                    =
                                                                    let uu____14769
                                                                    =
                                                                    let uu____14770
                                                                    =
                                                                    let uu____14776
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14776) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14770 in
                                                                    (uu____14769,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14765 in
                                                                    let uu____14783
                                                                    =
                                                                    let uu____14785
                                                                    =
                                                                    let uu____14786
                                                                    =
                                                                    let uu____14790
                                                                    =
                                                                    let uu____14791
                                                                    =
                                                                    let uu____14797
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14803
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14797,
                                                                    uu____14803) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14791 in
                                                                    (uu____14790,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14786 in
                                                                    [uu____14785] in
                                                                    uu____14764
                                                                    ::
                                                                    uu____14783 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14762 in
                                                                  FStar_List.append
                                                                    uu____14760
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14758 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14756 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14754 in
                                                          FStar_List.append
                                                            uu____14737
                                                            uu____14752 in
                                                        FStar_List.append
                                                          decls3 uu____14735 in
                                                      FStar_List.append
                                                        decls2 uu____14733 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14731 in
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
           (fun uu____14824  ->
              fun se  ->
                match uu____14824 with
                | (g,env1) ->
                    let uu____14836 = encode_sigelt env1 se in
                    (match uu____14836 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14872 =
        match uu____14872 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14890 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14895 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14895
                   then
                     let uu____14896 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14897 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14898 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14896 uu____14897 uu____14898
                   else ());
                  (let uu____14900 = encode_term t1 env1 in
                   match uu____14900 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14910 =
                         let uu____14914 =
                           let uu____14915 =
                             let uu____14916 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14916
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14915 in
                         new_term_constant_from_string env1 x uu____14914 in
                       (match uu____14910 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14927 = FStar_Options.log_queries () in
                              if uu____14927
                              then
                                let uu____14929 =
                                  let uu____14930 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14931 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14932 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14930 uu____14931 uu____14932 in
                                Some uu____14929
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14943,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14952 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14952 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14971 = encode_sigelt env1 se in
                 (match uu____14971 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14981 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14981 with | (uu____14993,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15038  ->
            match uu____15038 with
            | (l,uu____15045,uu____15046) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15067  ->
            match uu____15067 with
            | (l,uu____15075,uu____15076) ->
                let uu____15081 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____15082 =
                  let uu____15084 =
                    let uu____15085 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15085 in
                  [uu____15084] in
                uu____15081 :: uu____15082)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15096 =
      let uu____15098 =
        let uu____15099 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15101 =
          let uu____15102 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15102 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15099;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15101
        } in
      [uu____15098] in
    FStar_ST.write last_env uu____15096
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15112 = FStar_ST.read last_env in
      match uu____15112 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15118 ->
          let uu___154_15120 = e in
          let uu____15121 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15120.bindings);
            depth = (uu___154_15120.depth);
            tcenv;
            warn = (uu___154_15120.warn);
            cache = (uu___154_15120.cache);
            nolabels = (uu___154_15120.nolabels);
            use_zfuel_name = (uu___154_15120.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15120.encode_non_total_function_typ);
            current_module_name = uu____15121
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15125 = FStar_ST.read last_env in
    match uu____15125 with
    | [] -> failwith "Empty env stack"
    | uu____15130::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15138  ->
    let uu____15139 = FStar_ST.read last_env in
    match uu____15139 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15150 = hd1 in
          {
            bindings = (uu___155_15150.bindings);
            depth = (uu___155_15150.depth);
            tcenv = (uu___155_15150.tcenv);
            warn = (uu___155_15150.warn);
            cache = refs;
            nolabels = (uu___155_15150.nolabels);
            use_zfuel_name = (uu___155_15150.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15150.encode_non_total_function_typ);
            current_module_name = (uu___155_15150.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15156  ->
    let uu____15157 = FStar_ST.read last_env in
    match uu____15157 with
    | [] -> failwith "Popping an empty stack"
    | uu____15162::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15170  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15173  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15176  ->
    let uu____15177 = FStar_ST.read last_env in
    match uu____15177 with
    | hd1::uu____15183::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15189 -> failwith "Impossible"
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
        | (uu____15238::uu____15239,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15243 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15243.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15243.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15243.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15244 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15255 =
        let uu____15257 =
          let uu____15258 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15258 in
        let uu____15259 = open_fact_db_tags env in uu____15257 :: uu____15259 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15255
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
      let uu____15274 = encode_sigelt env se in
      match uu____15274 with
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
        let uu____15299 = FStar_Options.log_queries () in
        if uu____15299
        then
          let uu____15301 =
            let uu____15302 =
              let uu____15303 =
                let uu____15304 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15304 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15303 in
            FStar_SMTEncoding_Term.Caption uu____15302 in
          uu____15301 :: decls
        else decls in
      let env =
        let uu____15311 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15311 tcenv in
      let uu____15312 = encode_top_level_facts env se in
      match uu____15312 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15321 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15321))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15332 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15332
       then
         let uu____15333 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15333
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15354  ->
                 fun se  ->
                   match uu____15354 with
                   | (g,env2) ->
                       let uu____15366 = encode_top_level_facts env2 se in
                       (match uu____15366 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15379 =
         encode_signature
           (let uu___157_15383 = env in
            {
              bindings = (uu___157_15383.bindings);
              depth = (uu___157_15383.depth);
              tcenv = (uu___157_15383.tcenv);
              warn = false;
              cache = (uu___157_15383.cache);
              nolabels = (uu___157_15383.nolabels);
              use_zfuel_name = (uu___157_15383.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15383.encode_non_total_function_typ);
              current_module_name = (uu___157_15383.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15379 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15395 = FStar_Options.log_queries () in
             if uu____15395
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15400 = env1 in
               {
                 bindings = (uu___158_15400.bindings);
                 depth = (uu___158_15400.depth);
                 tcenv = (uu___158_15400.tcenv);
                 warn = true;
                 cache = (uu___158_15400.cache);
                 nolabels = (uu___158_15400.nolabels);
                 use_zfuel_name = (uu___158_15400.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15400.encode_non_total_function_typ);
                 current_module_name = (uu___158_15400.current_module_name)
               });
            (let uu____15402 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15402
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
        (let uu____15437 =
           let uu____15438 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15438.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15437);
        (let env =
           let uu____15440 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15440 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15447 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15468 = aux rest in
                 (match uu____15468 with
                  | (out,rest1) ->
                      let t =
                        let uu____15486 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15486 with
                        | Some uu____15490 ->
                            let uu____15491 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15491
                              x.FStar_Syntax_Syntax.sort
                        | uu____15492 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15495 =
                        let uu____15497 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_15498 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_15498.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_15498.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15497 :: out in
                      (uu____15495, rest1))
             | uu____15501 -> ([], bindings1) in
           let uu____15505 = aux bindings in
           match uu____15505 with
           | (closing,bindings1) ->
               let uu____15519 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15519, bindings1) in
         match uu____15447 with
         | (q1,bindings1) ->
             let uu____15532 =
               let uu____15535 =
                 FStar_List.filter
                   (fun uu___125_15537  ->
                      match uu___125_15537 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15538 ->
                          false
                      | uu____15542 -> true) bindings1 in
               encode_env_bindings env uu____15535 in
             (match uu____15532 with
              | (env_decls,env1) ->
                  ((let uu____15553 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15553
                    then
                      let uu____15554 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15554
                    else ());
                   (let uu____15556 = encode_formula q1 env1 in
                    match uu____15556 with
                    | (phi,qdecls) ->
                        let uu____15568 =
                          let uu____15571 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15571 phi in
                        (match uu____15568 with
                         | (labels,phi1) ->
                             let uu____15581 = encode_labels labels in
                             (match uu____15581 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15602 =
                                      let uu____15606 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15607 =
                                        varops.mk_unique "@query" in
                                      (uu____15606, (Some "query"),
                                        uu____15607) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15602 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15620 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15620 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15622 = encode_formula q env in
       match uu____15622 with
       | (f,uu____15626) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15628) -> true
             | uu____15631 -> false)))