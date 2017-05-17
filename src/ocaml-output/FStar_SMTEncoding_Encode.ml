open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___102_74  ->
       match uu___102_74 with
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
        let uu___127_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___127_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___127_140.FStar_Syntax_Syntax.sort)
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
    let uu___128_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___128_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___128_780.FStar_Syntax_Syntax.sort)
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
         (fun uu___103_1001  ->
            match uu___103_1001 with
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
           (fun uu___104_1016  ->
              match uu___104_1016 with
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
        (let uu___129_1080 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___129_1080.tcenv);
           warn = (uu___129_1080.warn);
           cache = (uu___129_1080.cache);
           nolabels = (uu___129_1080.nolabels);
           use_zfuel_name = (uu___129_1080.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___129_1080.encode_non_total_function_typ);
           current_module_name = (uu___129_1080.current_module_name)
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
        (let uu___130_1093 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___130_1093.depth);
           tcenv = (uu___130_1093.tcenv);
           warn = (uu___130_1093.warn);
           cache = (uu___130_1093.cache);
           nolabels = (uu___130_1093.nolabels);
           use_zfuel_name = (uu___130_1093.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___130_1093.encode_non_total_function_typ);
           current_module_name = (uu___130_1093.current_module_name)
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
          (let uu___131_1109 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___131_1109.depth);
             tcenv = (uu___131_1109.tcenv);
             warn = (uu___131_1109.warn);
             cache = (uu___131_1109.cache);
             nolabels = (uu___131_1109.nolabels);
             use_zfuel_name = (uu___131_1109.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___131_1109.encode_non_total_function_typ);
             current_module_name = (uu___131_1109.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___132_1119 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___132_1119.depth);
          tcenv = (uu___132_1119.tcenv);
          warn = (uu___132_1119.warn);
          cache = (uu___132_1119.cache);
          nolabels = (uu___132_1119.nolabels);
          use_zfuel_name = (uu___132_1119.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___132_1119.encode_non_total_function_typ);
          current_module_name = (uu___132_1119.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___105_1135  ->
             match uu___105_1135 with
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
        let uu___133_1182 = env in
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
          depth = (uu___133_1182.depth);
          tcenv = (uu___133_1182.tcenv);
          warn = (uu___133_1182.warn);
          cache = (uu___133_1182.cache);
          nolabels = (uu___133_1182.nolabels);
          use_zfuel_name = (uu___133_1182.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___133_1182.encode_non_total_function_typ);
          current_module_name = (uu___133_1182.current_module_name)
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
        (fun uu___106_1217  ->
           match uu___106_1217 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1239 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1251 =
        lookup_binding env
          (fun uu___107_1253  ->
             match uu___107_1253 with
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
          let uu___134_1325 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___134_1325.depth);
            tcenv = (uu___134_1325.tcenv);
            warn = (uu___134_1325.warn);
            cache = (uu___134_1325.cache);
            nolabels = (uu___134_1325.nolabels);
            use_zfuel_name = (uu___134_1325.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___134_1325.encode_non_total_function_typ);
            current_module_name = (uu___134_1325.current_module_name)
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
            let uu___135_1360 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___135_1360.depth);
              tcenv = (uu___135_1360.tcenv);
              warn = (uu___135_1360.warn);
              cache = (uu___135_1360.cache);
              nolabels = (uu___135_1360.nolabels);
              use_zfuel_name = (uu___135_1360.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___135_1360.encode_non_total_function_typ);
              current_module_name = (uu___135_1360.current_module_name)
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
        (fun uu___108_1538  ->
           match uu___108_1538 with
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
               (fun uu___109_1723  ->
                  match uu___109_1723 with
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
  fun uu___110_1828  ->
    match uu___110_1828 with
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
  fun uu___111_1985  ->
    match uu___111_1985 with
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
        (let uu____2218 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2218
         then
           let uu____2219 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2219
         else ());
        (let uu____2221 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2257  ->
                   fun b  ->
                     match uu____2257 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2300 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2309 = gen_term_var env1 x in
                           match uu____2309 with
                           | (xxsym,xx,env') ->
                               let uu____2323 =
                                 let uu____2326 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2326 env1 xx in
                               (match uu____2323 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2300 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2221 with
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
          let uu____2414 = encode_term t env in
          match uu____2414 with
          | (t1,decls) ->
              let uu____2421 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2421, decls)
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
          let uu____2429 = encode_term t env in
          match uu____2429 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2438 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2438, decls)
               | Some f ->
                   let uu____2440 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2440, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2447 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2447
       then
         let uu____2448 = FStar_Syntax_Print.tag_of_term t in
         let uu____2449 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2450 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2448 uu____2449
           uu____2450
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2455 =
             let uu____2456 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2457 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2458 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2459 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2456
               uu____2457 uu____2458 uu____2459 in
           failwith uu____2455
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2463 =
             let uu____2464 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2464 in
           failwith uu____2463
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2469) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2499) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2508 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2508, [])
       | FStar_Syntax_Syntax.Tm_type uu____2514 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2517) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2523 = encode_const c in (uu____2523, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2538 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2538 with
            | (binders1,res) ->
                let uu____2545 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2545
                then
                  let uu____2548 = encode_binders None binders1 env in
                  (match uu____2548 with
                   | (vars,guards,env',decls,uu____2563) ->
                       let fsym =
                         let uu____2573 = varops.fresh "f" in
                         (uu____2573, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2576 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___136_2580 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___136_2580.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___136_2580.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___136_2580.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___136_2580.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___136_2580.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___136_2580.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___136_2580.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___136_2580.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___136_2580.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___136_2580.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___136_2580.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___136_2580.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___136_2580.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___136_2580.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___136_2580.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___136_2580.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___136_2580.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___136_2580.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___136_2580.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___136_2580.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___136_2580.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___136_2580.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___136_2580.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___136_2580.FStar_TypeChecker_Env.proof_ns)
                            }) res in
                       (match uu____2576 with
                        | (pre_opt,res_t) ->
                            let uu____2587 =
                              encode_term_pred None res_t env' app in
                            (match uu____2587 with
                             | (res_pred,decls') ->
                                 let uu____2594 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2601 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2601, [])
                                   | Some pre ->
                                       let uu____2604 =
                                         encode_formula pre env' in
                                       (match uu____2604 with
                                        | (guard,decls0) ->
                                            let uu____2612 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2612, decls0)) in
                                 (match uu____2594 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2620 =
                                          let uu____2626 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2626) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2620 in
                                      let cvars =
                                        let uu____2636 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2636
                                          (FStar_List.filter
                                             (fun uu____2642  ->
                                                match uu____2642 with
                                                | (x,uu____2646) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2657 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2657 with
                                       | Some cache_entry ->
                                           let uu____2662 =
                                             let uu____2663 =
                                               let uu____2667 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2667) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2663 in
                                           (uu____2662,
                                             (use_cache_entry cache_entry))
                                       | None  ->
                                           let tsym =
                                             let uu____2678 =
                                               let uu____2679 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2679 in
                                             varops.mk_unique uu____2678 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2686 =
                                               FStar_Options.log_queries () in
                                             if uu____2686
                                             then
                                               let uu____2688 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2688
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2694 =
                                               let uu____2698 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2698) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2694 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2706 =
                                               let uu____2710 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2710, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2706 in
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
                                             let uu____2723 =
                                               let uu____2727 =
                                                 let uu____2728 =
                                                   let uu____2734 =
                                                     let uu____2735 =
                                                       let uu____2738 =
                                                         let uu____2739 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2739 in
                                                       (f_has_t, uu____2738) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2735 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2734) in
                                                 mkForall_fuel uu____2728 in
                                               (uu____2727,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2723 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2752 =
                                               let uu____2756 =
                                                 let uu____2757 =
                                                   let uu____2763 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2763) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2757 in
                                               (uu____2756, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2752 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2777 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2777);
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
                     let uu____2788 =
                       let uu____2792 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2792, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2788 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2801 =
                       let uu____2805 =
                         let uu____2806 =
                           let uu____2812 =
                             let uu____2813 =
                               let uu____2816 =
                                 let uu____2817 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2817 in
                               (f_has_t, uu____2816) in
                             FStar_SMTEncoding_Util.mkImp uu____2813 in
                           ([[f_has_t]], [fsym], uu____2812) in
                         mkForall_fuel uu____2806 in
                       (uu____2805, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2801 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2831 ->
           let uu____2836 =
             let uu____2839 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2839 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2844;
                 FStar_Syntax_Syntax.pos = uu____2845;
                 FStar_Syntax_Syntax.vars = uu____2846;_} ->
                 let uu____2853 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2853 with
                  | (b,f1) ->
                      let uu____2867 =
                        let uu____2868 = FStar_List.hd b in
                        Prims.fst uu____2868 in
                      (uu____2867, f1))
             | uu____2873 -> failwith "impossible" in
           (match uu____2836 with
            | (x,f) ->
                let uu____2880 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2880 with
                 | (base_t,decls) ->
                     let uu____2887 = gen_term_var env x in
                     (match uu____2887 with
                      | (x1,xtm,env') ->
                          let uu____2896 = encode_formula f env' in
                          (match uu____2896 with
                           | (refinement,decls') ->
                               let uu____2903 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2903 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2914 =
                                        let uu____2916 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2920 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2916
                                          uu____2920 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2914 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2936  ->
                                              match uu____2936 with
                                              | (y,uu____2940) ->
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
                                    let uu____2959 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2959 with
                                     | Some cache_entry ->
                                         let uu____2964 =
                                           let uu____2965 =
                                             let uu____2969 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____2969) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2965 in
                                         (uu____2964,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____2981 =
                                             let uu____2982 =
                                               let uu____2983 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____2983 in
                                             Prims.strcat module_name
                                               uu____2982 in
                                           varops.mk_unique uu____2981 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2992 =
                                             let uu____2996 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____2996) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2992 in
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
                                           let uu____3006 =
                                             let uu____3010 =
                                               let uu____3011 =
                                                 let uu____3017 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3017) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3011 in
                                             (uu____3010,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3006 in
                                         let t_kinding =
                                           let uu____3027 =
                                             let uu____3031 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3031,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3027 in
                                         let t_interp =
                                           let uu____3041 =
                                             let uu____3045 =
                                               let uu____3046 =
                                                 let uu____3052 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3052) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3046 in
                                             let uu____3064 =
                                               let uu____3066 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3066 in
                                             (uu____3045, uu____3064,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3041 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3071 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3071);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3088 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3088 in
           let uu____3092 = encode_term_pred None k env ttm in
           (match uu____3092 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3100 =
                    let uu____3104 =
                      let uu____3105 =
                        let uu____3106 =
                          let uu____3107 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3107 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3106 in
                      varops.mk_unique uu____3105 in
                    (t_has_k, (Some "Uvar typing"), uu____3104) in
                  FStar_SMTEncoding_Util.mkAssume uu____3100 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3113 ->
           let uu____3123 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3123 with
            | (head1,args_e) ->
                let uu____3151 =
                  let uu____3159 =
                    let uu____3160 = FStar_Syntax_Subst.compress head1 in
                    uu____3160.FStar_Syntax_Syntax.n in
                  (uu____3159, args_e) in
                (match uu____3151 with
                 | (uu____3170,uu____3171) when head_redex env head1 ->
                     let uu____3182 = whnf env t in
                     encode_term uu____3182 env
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
                     let uu____3256 = encode_term v1 env in
                     (match uu____3256 with
                      | (v11,decls1) ->
                          let uu____3263 = encode_term v2 env in
                          (match uu____3263 with
                           | (v21,decls2) ->
                               let uu____3270 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3270,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3272) ->
                     let e0 =
                       let uu____3284 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3284 in
                     ((let uu____3290 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3290
                       then
                         let uu____3291 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3291
                       else ());
                      (let e =
                         let uu____3296 =
                           let uu____3297 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3298 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3297
                             uu____3298 in
                         uu____3296 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3307),(arg,uu____3309)::[]) -> encode_term arg env
                 | uu____3327 ->
                     let uu____3335 = encode_args args_e env in
                     (match uu____3335 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3368 = encode_term head1 env in
                            match uu____3368 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3407 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3407 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3449  ->
                                                 fun uu____3450  ->
                                                   match (uu____3449,
                                                           uu____3450)
                                                   with
                                                   | ((bv,uu____3464),
                                                      (a,uu____3466)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3480 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3480
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3485 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3485 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3495 =
                                                   let uu____3499 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3504 =
                                                     let uu____3505 =
                                                       let uu____3506 =
                                                         let uu____3507 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3507 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3506 in
                                                     varops.mk_unique
                                                       uu____3505 in
                                                   (uu____3499,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3504) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3495 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3524 = lookup_free_var_sym env fv in
                            match uu____3524 with
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
                                let uu____3562 =
                                  let uu____3563 =
                                    let uu____3566 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3566 Prims.fst in
                                  FStar_All.pipe_right uu____3563 Prims.snd in
                                Some uu____3562
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3585,(FStar_Util.Inl t1,uu____3587),uu____3588)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3626,(FStar_Util.Inr c,uu____3628),uu____3629)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3667 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3687 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3687 in
                               let uu____3688 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3688 with
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
                                     | uu____3713 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3758 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3758 with
            | (bs1,body1,opening) ->
                let fallback uu____3773 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3778 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3778, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3789 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3789
                  | FStar_Util.Inr (eff,uu____3791) ->
                      let uu____3797 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3797 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3842 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___137_3843 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___137_3843.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___137_3843.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___137_3843.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___137_3843.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___137_3843.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___137_3843.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___137_3843.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___137_3843.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___137_3843.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___137_3843.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___137_3843.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___137_3843.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___137_3843.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___137_3843.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___137_3843.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___137_3843.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___137_3843.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___137_3843.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___137_3843.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___137_3843.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___137_3843.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___137_3843.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___137_3843.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___137_3843.FStar_TypeChecker_Env.proof_ns)
                             }) uu____3842 FStar_Syntax_Syntax.U_unknown in
                        let uu____3844 =
                          let uu____3845 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3845 in
                        FStar_Util.Inl uu____3844
                    | FStar_Util.Inr (eff_name,uu____3852) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3883 =
                        let uu____3884 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____3884 in
                      FStar_All.pipe_right uu____3883
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____3896 =
                        let uu____3897 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____3897 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____3905 =
                          let uu____3906 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____3906 in
                        FStar_All.pipe_right uu____3905
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____3910 =
                             let uu____3911 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____3911 in
                           FStar_All.pipe_right uu____3910
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____3922 =
                         let uu____3923 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____3923 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____3922);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____3938 =
                       (is_impure lc1) &&
                         (let uu____3939 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____3939) in
                     if uu____3938
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____3944 = encode_binders None bs1 env in
                        match uu____3944 with
                        | (vars,guards,envbody,decls,uu____3959) ->
                            let uu____3966 =
                              let uu____3974 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____3974
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____3966 with
                             | (lc2,body2) ->
                                 let uu____3999 = encode_term body2 envbody in
                                 (match uu____3999 with
                                  | (body3,decls') ->
                                      let uu____4006 =
                                        let uu____4011 = codomain_eff lc2 in
                                        match uu____4011 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4023 =
                                              encode_term tfun env in
                                            (match uu____4023 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4006 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4042 =
                                               let uu____4048 =
                                                 let uu____4049 =
                                                   let uu____4052 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4052, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4049 in
                                               ([], vars, uu____4048) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4042 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4060 =
                                                   let uu____4062 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4062 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4060 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4073 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4073 with
                                            | Some cache_entry ->
                                                let uu____4078 =
                                                  let uu____4079 =
                                                    let uu____4083 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4083) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4079 in
                                                (uu____4078,
                                                  (use_cache_entry
                                                     cache_entry))
                                            | None  ->
                                                let uu____4089 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4089 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4096 =
                                                         let uu____4097 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4097 =
                                                           cache_size in
                                                       if uu____4096
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
                                                         let uu____4108 =
                                                           let uu____4109 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4109 in
                                                         varops.mk_unique
                                                           uu____4108 in
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
                                                       let uu____4114 =
                                                         let uu____4118 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4118) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4114 in
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
                                                           let uu____4130 =
                                                             let uu____4131 =
                                                               let uu____4135
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4135,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4131 in
                                                           [uu____4130] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4143 =
                                                         let uu____4147 =
                                                           let uu____4148 =
                                                             let uu____4154 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4154) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4148 in
                                                         (uu____4147,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4143 in
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
                                                     ((let uu____4164 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4164);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4166,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4167;
                          FStar_Syntax_Syntax.lbunivs = uu____4168;
                          FStar_Syntax_Syntax.lbtyp = uu____4169;
                          FStar_Syntax_Syntax.lbeff = uu____4170;
                          FStar_Syntax_Syntax.lbdef = uu____4171;_}::uu____4172),uu____4173)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4191;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4193;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4209 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4222 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4222, [decl_e])))
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
              let uu____4264 = encode_term e1 env in
              match uu____4264 with
              | (ee1,decls1) ->
                  let uu____4271 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4271 with
                   | (xs,e21) ->
                       let uu____4285 = FStar_List.hd xs in
                       (match uu____4285 with
                        | (x1,uu____4293) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4295 = encode_body e21 env' in
                            (match uu____4295 with
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
            let uu____4317 =
              let uu____4321 =
                let uu____4322 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4322 in
              gen_term_var env uu____4321 in
            match uu____4317 with
            | (scrsym,scr',env1) ->
                let uu____4336 = encode_term e env1 in
                (match uu____4336 with
                 | (scr,decls) ->
                     let uu____4343 =
                       let encode_branch b uu____4359 =
                         match uu____4359 with
                         | (else_case,decls1) ->
                             let uu____4370 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4370 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4400  ->
                                       fun uu____4401  ->
                                         match (uu____4400, uu____4401) with
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
                                                       fun uu____4438  ->
                                                         match uu____4438
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4443 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4458 =
                                                     encode_term w1 env2 in
                                                   (match uu____4458 with
                                                    | (w2,decls21) ->
                                                        let uu____4466 =
                                                          let uu____4467 =
                                                            let uu____4470 =
                                                              let uu____4471
                                                                =
                                                                let uu____4474
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4474) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4471 in
                                                            (guard,
                                                              uu____4470) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4467 in
                                                        (uu____4466, decls21)) in
                                             (match uu____4443 with
                                              | (guard1,decls21) ->
                                                  let uu____4482 =
                                                    encode_br br env2 in
                                                  (match uu____4482 with
                                                   | (br1,decls3) ->
                                                       let uu____4490 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4490,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4343 with
                      | (match_tm,decls1) ->
                          let uu____4502 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4502, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4533 -> let uu____4534 = encode_one_pat env pat in [uu____4534]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4546 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4546
       then
         let uu____4547 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4547
       else ());
      (let uu____4549 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4549 with
       | (vars,pat_term) ->
           let uu____4559 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4582  ->
                     fun v1  ->
                       match uu____4582 with
                       | (env1,vars1) ->
                           let uu____4610 = gen_term_var env1 v1 in
                           (match uu____4610 with
                            | (xx,uu____4622,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4559 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4669 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4677 =
                        let uu____4680 = encode_const c in
                        (scrutinee, uu____4680) in
                      FStar_SMTEncoding_Util.mkEq uu____4677
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4699 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4699 with
                        | (uu____4703,uu____4704::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4706 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4727  ->
                                  match uu____4727 with
                                  | (arg,uu____4733) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4743 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4743)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4762 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4777 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4792 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4814  ->
                                  match uu____4814 with
                                  | (arg,uu____4823) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4833 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4833)) in
                      FStar_All.pipe_right uu____4792 FStar_List.flatten in
                let pat_term1 uu____4849 = encode_term pat_term env1 in
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
      let uu____4856 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4871  ->
                fun uu____4872  ->
                  match (uu____4871, uu____4872) with
                  | ((tms,decls),(t,uu____4892)) ->
                      let uu____4903 = encode_term t env in
                      (match uu____4903 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4856 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____4937 = FStar_Syntax_Util.list_elements e in
        match uu____4937 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____4955 =
          let uu____4965 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____4965 FStar_Syntax_Util.head_and_args in
        match uu____4955 with
        | (head1,args) ->
            let uu____4996 =
              let uu____5004 =
                let uu____5005 = FStar_Syntax_Util.un_uinst head1 in
                uu____5005.FStar_Syntax_Syntax.n in
              (uu____5004, args) in
            (match uu____4996 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5019,uu____5020)::(e,uu____5022)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5053)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5074 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5107 =
            let uu____5117 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5117 FStar_Syntax_Util.head_and_args in
          match uu____5107 with
          | (head1,args) ->
              let uu____5146 =
                let uu____5154 =
                  let uu____5155 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5155.FStar_Syntax_Syntax.n in
                (uu____5154, args) in
              (match uu____5146 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5168)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5188 -> None) in
        match elts with
        | t1::[] ->
            let uu____5206 = smt_pat_or t1 in
            (match uu____5206 with
             | Some e ->
                 let uu____5222 = list_elements1 e in
                 FStar_All.pipe_right uu____5222
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5239 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5239
                           (FStar_List.map one_pat)))
             | uu____5253 ->
                 let uu____5257 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5257])
        | uu____5288 ->
            let uu____5290 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5290] in
      let uu____5321 =
        let uu____5337 =
          let uu____5338 = FStar_Syntax_Subst.compress t in
          uu____5338.FStar_Syntax_Syntax.n in
        match uu____5337 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5368 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5368 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5403;
                        FStar_Syntax_Syntax.effect_name = uu____5404;
                        FStar_Syntax_Syntax.result_typ = uu____5405;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5407)::(post,uu____5409)::(pats,uu____5411)::[];
                        FStar_Syntax_Syntax.flags = uu____5412;_}
                      ->
                      let uu____5444 = lemma_pats pats in
                      (binders1, pre, post, uu____5444)
                  | uu____5463 -> failwith "impos"))
        | uu____5479 -> failwith "Impos" in
      match uu____5321 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___138_5524 = env in
            {
              bindings = (uu___138_5524.bindings);
              depth = (uu___138_5524.depth);
              tcenv = (uu___138_5524.tcenv);
              warn = (uu___138_5524.warn);
              cache = (uu___138_5524.cache);
              nolabels = (uu___138_5524.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___138_5524.encode_non_total_function_typ);
              current_module_name = (uu___138_5524.current_module_name)
            } in
          let uu____5525 = encode_binders None binders env1 in
          (match uu____5525 with
           | (vars,guards,env2,decls,uu____5540) ->
               let uu____5547 =
                 let uu____5554 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5585 =
                             let uu____5590 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____5606  ->
                                       match uu____5606 with
                                       | (t1,uu____5613) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5590 FStar_List.unzip in
                           match uu____5585 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5554 FStar_List.unzip in
               (match uu____5547 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___139_5663 = env2 in
                      {
                        bindings = (uu___139_5663.bindings);
                        depth = (uu___139_5663.depth);
                        tcenv = (uu___139_5663.tcenv);
                        warn = (uu___139_5663.warn);
                        cache = (uu___139_5663.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___139_5663.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___139_5663.encode_non_total_function_typ);
                        current_module_name =
                          (uu___139_5663.current_module_name)
                      } in
                    let uu____5664 =
                      let uu____5667 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5667 env3 in
                    (match uu____5664 with
                     | (pre1,decls'') ->
                         let uu____5672 =
                           let uu____5675 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5675 env3 in
                         (match uu____5672 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____5682 =
                                let uu____5683 =
                                  let uu____5689 =
                                    let uu____5690 =
                                      let uu____5693 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____5693, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____5690 in
                                  (pats, vars, uu____5689) in
                                FStar_SMTEncoding_Util.mkForall uu____5683 in
                              (uu____5682, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5706 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5706
        then
          let uu____5707 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5708 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5707 uu____5708
        else () in
      let enc f r l =
        let uu____5735 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5748 = encode_term (Prims.fst x) env in
                 match uu____5748 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5735 with
        | (decls,args) ->
            let uu____5765 =
              let uu___140_5766 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_5766.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_5766.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5765, decls) in
      let const_op f r uu____5785 = let uu____5788 = f r in (uu____5788, []) in
      let un_op f l =
        let uu____5804 = FStar_List.hd l in FStar_All.pipe_left f uu____5804 in
      let bin_op f uu___112_5817 =
        match uu___112_5817 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5825 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5852 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5861  ->
                 match uu____5861 with
                 | (t,uu____5869) ->
                     let uu____5870 = encode_formula t env in
                     (match uu____5870 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____5852 with
        | (decls,phis) ->
            let uu____5887 =
              let uu___141_5888 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___141_5888.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___141_5888.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5887, decls) in
      let eq_op r uu___113_5904 =
        match uu___113_5904 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____5964 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____5964 r [e1; e2]
        | l ->
            let uu____5984 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____5984 r l in
      let mk_imp1 r uu___114_6003 =
        match uu___114_6003 with
        | (lhs,uu____6007)::(rhs,uu____6009)::[] ->
            let uu____6030 = encode_formula rhs env in
            (match uu____6030 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6039) ->
                      (l1, decls1)
                  | uu____6042 ->
                      let uu____6043 = encode_formula lhs env in
                      (match uu____6043 with
                       | (l2,decls2) ->
                           let uu____6050 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6050, (FStar_List.append decls1 decls2)))))
        | uu____6052 -> failwith "impossible" in
      let mk_ite r uu___115_6067 =
        match uu___115_6067 with
        | (guard,uu____6071)::(_then,uu____6073)::(_else,uu____6075)::[] ->
            let uu____6104 = encode_formula guard env in
            (match uu____6104 with
             | (g,decls1) ->
                 let uu____6111 = encode_formula _then env in
                 (match uu____6111 with
                  | (t,decls2) ->
                      let uu____6118 = encode_formula _else env in
                      (match uu____6118 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6127 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6146 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6146 in
      let connectives =
        let uu____6158 =
          let uu____6167 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6167) in
        let uu____6180 =
          let uu____6190 =
            let uu____6199 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6199) in
          let uu____6212 =
            let uu____6222 =
              let uu____6232 =
                let uu____6241 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6241) in
              let uu____6254 =
                let uu____6264 =
                  let uu____6274 =
                    let uu____6283 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6283) in
                  [uu____6274;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6264 in
              uu____6232 :: uu____6254 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6222 in
          uu____6190 :: uu____6212 in
        uu____6158 :: uu____6180 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6445 = encode_formula phi' env in
            (match uu____6445 with
             | (phi2,decls) ->
                 let uu____6452 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6452, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6453 ->
            let uu____6458 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6458 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6487 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6487 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6495;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6497;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6513 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6513 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6545::(x,uu____6547)::(t,uu____6549)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6583 = encode_term x env in
                 (match uu____6583 with
                  | (x1,decls) ->
                      let uu____6590 = encode_term t env in
                      (match uu____6590 with
                       | (t1,decls') ->
                           let uu____6597 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6597, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6601)::(msg,uu____6603)::(phi2,uu____6605)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6639 =
                   let uu____6642 =
                     let uu____6643 = FStar_Syntax_Subst.compress r in
                     uu____6643.FStar_Syntax_Syntax.n in
                   let uu____6646 =
                     let uu____6647 = FStar_Syntax_Subst.compress msg in
                     uu____6647.FStar_Syntax_Syntax.n in
                   (uu____6642, uu____6646) in
                 (match uu____6639 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6654))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6670 -> fallback phi2)
             | uu____6673 when head_redex env head2 ->
                 let uu____6681 = whnf env phi1 in
                 encode_formula uu____6681 env
             | uu____6682 ->
                 let uu____6690 = encode_term phi1 env in
                 (match uu____6690 with
                  | (tt,decls) ->
                      let uu____6697 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___142_6698 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___142_6698.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___142_6698.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6697, decls)))
        | uu____6701 ->
            let uu____6702 = encode_term phi1 env in
            (match uu____6702 with
             | (tt,decls) ->
                 let uu____6709 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___143_6710 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___143_6710.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___143_6710.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6709, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6737 = encode_binders None bs env1 in
        match uu____6737 with
        | (vars,guards,env2,decls,uu____6759) ->
            let uu____6766 =
              let uu____6773 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6796 =
                          let uu____6801 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6815  ->
                                    match uu____6815 with
                                    | (t,uu____6821) ->
                                        encode_term t
                                          (let uu___144_6822 = env2 in
                                           {
                                             bindings =
                                               (uu___144_6822.bindings);
                                             depth = (uu___144_6822.depth);
                                             tcenv = (uu___144_6822.tcenv);
                                             warn = (uu___144_6822.warn);
                                             cache = (uu___144_6822.cache);
                                             nolabels =
                                               (uu___144_6822.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___144_6822.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___144_6822.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____6801 FStar_List.unzip in
                        match uu____6796 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6773 FStar_List.unzip in
            (match uu____6766 with
             | (pats,decls') ->
                 let uu____6874 = encode_formula body env2 in
                 (match uu____6874 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6893;
                             FStar_SMTEncoding_Term.rng = uu____6894;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6902 -> guards in
                      let uu____6905 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____6905, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____6939  ->
                   match uu____6939 with
                   | (x,uu____6943) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____6949 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____6955 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____6955) uu____6949 tl1 in
             let uu____6957 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____6969  ->
                       match uu____6969 with
                       | (b,uu____6973) ->
                           let uu____6974 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____6974)) in
             (match uu____6957 with
              | None  -> ()
              | Some (x,uu____6978) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____6988 =
                    let uu____6989 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____6989 in
                  FStar_Errors.warn pos uu____6988) in
       let uu____6990 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____6990 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____6996 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7032  ->
                     match uu____7032 with
                     | (l,uu____7042) -> FStar_Ident.lid_equals op l)) in
           (match uu____6996 with
            | None  -> fallback phi1
            | Some (uu____7065,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7094 = encode_q_body env vars pats body in
             match uu____7094 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7120 =
                     let uu____7126 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7126) in
                   FStar_SMTEncoding_Term.mkForall uu____7120
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7138 = encode_q_body env vars pats body in
             match uu____7138 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7163 =
                   let uu____7164 =
                     let uu____7170 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7170) in
                   FStar_SMTEncoding_Term.mkExists uu____7164
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7163, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7219 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7219 with
  | (asym,a) ->
      let uu____7224 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7224 with
       | (xsym,x) ->
           let uu____7229 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7229 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7259 =
                      let uu____7265 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7265, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7259 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7280 =
                      let uu____7284 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7284) in
                    FStar_SMTEncoding_Util.mkApp uu____7280 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7292 =
                    let uu____7294 =
                      let uu____7296 =
                        let uu____7298 =
                          let uu____7299 =
                            let uu____7303 =
                              let uu____7304 =
                                let uu____7310 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7310) in
                              FStar_SMTEncoding_Util.mkForall uu____7304 in
                            (uu____7303, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7299 in
                        let uu____7319 =
                          let uu____7321 =
                            let uu____7322 =
                              let uu____7326 =
                                let uu____7327 =
                                  let uu____7333 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7333) in
                                FStar_SMTEncoding_Util.mkForall uu____7327 in
                              (uu____7326,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7322 in
                          [uu____7321] in
                        uu____7298 :: uu____7319 in
                      xtok_decl :: uu____7296 in
                    xname_decl :: uu____7294 in
                  (xtok1, uu____7292) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7382 =
                    let uu____7390 =
                      let uu____7396 =
                        let uu____7397 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7397 in
                      quant axy uu____7396 in
                    (FStar_Syntax_Const.op_Eq, uu____7390) in
                  let uu____7403 =
                    let uu____7412 =
                      let uu____7420 =
                        let uu____7426 =
                          let uu____7427 =
                            let uu____7428 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7428 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7427 in
                        quant axy uu____7426 in
                      (FStar_Syntax_Const.op_notEq, uu____7420) in
                    let uu____7434 =
                      let uu____7443 =
                        let uu____7451 =
                          let uu____7457 =
                            let uu____7458 =
                              let uu____7459 =
                                let uu____7462 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7463 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7462, uu____7463) in
                              FStar_SMTEncoding_Util.mkLT uu____7459 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7458 in
                          quant xy uu____7457 in
                        (FStar_Syntax_Const.op_LT, uu____7451) in
                      let uu____7469 =
                        let uu____7478 =
                          let uu____7486 =
                            let uu____7492 =
                              let uu____7493 =
                                let uu____7494 =
                                  let uu____7497 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7498 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7497, uu____7498) in
                                FStar_SMTEncoding_Util.mkLTE uu____7494 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7493 in
                            quant xy uu____7492 in
                          (FStar_Syntax_Const.op_LTE, uu____7486) in
                        let uu____7504 =
                          let uu____7513 =
                            let uu____7521 =
                              let uu____7527 =
                                let uu____7528 =
                                  let uu____7529 =
                                    let uu____7532 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7533 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7532, uu____7533) in
                                  FStar_SMTEncoding_Util.mkGT uu____7529 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7528 in
                              quant xy uu____7527 in
                            (FStar_Syntax_Const.op_GT, uu____7521) in
                          let uu____7539 =
                            let uu____7548 =
                              let uu____7556 =
                                let uu____7562 =
                                  let uu____7563 =
                                    let uu____7564 =
                                      let uu____7567 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7568 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7567, uu____7568) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7564 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7563 in
                                quant xy uu____7562 in
                              (FStar_Syntax_Const.op_GTE, uu____7556) in
                            let uu____7574 =
                              let uu____7583 =
                                let uu____7591 =
                                  let uu____7597 =
                                    let uu____7598 =
                                      let uu____7599 =
                                        let uu____7602 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7603 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7602, uu____7603) in
                                      FStar_SMTEncoding_Util.mkSub uu____7599 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7598 in
                                  quant xy uu____7597 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7591) in
                              let uu____7609 =
                                let uu____7618 =
                                  let uu____7626 =
                                    let uu____7632 =
                                      let uu____7633 =
                                        let uu____7634 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7634 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7633 in
                                    quant qx uu____7632 in
                                  (FStar_Syntax_Const.op_Minus, uu____7626) in
                                let uu____7640 =
                                  let uu____7649 =
                                    let uu____7657 =
                                      let uu____7663 =
                                        let uu____7664 =
                                          let uu____7665 =
                                            let uu____7668 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7669 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7668, uu____7669) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7665 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7664 in
                                      quant xy uu____7663 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7657) in
                                  let uu____7675 =
                                    let uu____7684 =
                                      let uu____7692 =
                                        let uu____7698 =
                                          let uu____7699 =
                                            let uu____7700 =
                                              let uu____7703 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7704 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7703, uu____7704) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7700 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7699 in
                                        quant xy uu____7698 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7692) in
                                    let uu____7710 =
                                      let uu____7719 =
                                        let uu____7727 =
                                          let uu____7733 =
                                            let uu____7734 =
                                              let uu____7735 =
                                                let uu____7738 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7739 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7738, uu____7739) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7735 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7734 in
                                          quant xy uu____7733 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7727) in
                                      let uu____7745 =
                                        let uu____7754 =
                                          let uu____7762 =
                                            let uu____7768 =
                                              let uu____7769 =
                                                let uu____7770 =
                                                  let uu____7773 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7774 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7773, uu____7774) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7770 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7769 in
                                            quant xy uu____7768 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7762) in
                                        let uu____7780 =
                                          let uu____7789 =
                                            let uu____7797 =
                                              let uu____7803 =
                                                let uu____7804 =
                                                  let uu____7805 =
                                                    let uu____7808 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7809 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7808, uu____7809) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7805 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7804 in
                                              quant xy uu____7803 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7797) in
                                          let uu____7815 =
                                            let uu____7824 =
                                              let uu____7832 =
                                                let uu____7838 =
                                                  let uu____7839 =
                                                    let uu____7840 =
                                                      let uu____7843 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7844 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7843,
                                                        uu____7844) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7840 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7839 in
                                                quant xy uu____7838 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7832) in
                                            let uu____7850 =
                                              let uu____7859 =
                                                let uu____7867 =
                                                  let uu____7873 =
                                                    let uu____7874 =
                                                      let uu____7875 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7875 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7874 in
                                                  quant qx uu____7873 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7867) in
                                              [uu____7859] in
                                            uu____7824 :: uu____7850 in
                                          uu____7789 :: uu____7815 in
                                        uu____7754 :: uu____7780 in
                                      uu____7719 :: uu____7745 in
                                    uu____7684 :: uu____7710 in
                                  uu____7649 :: uu____7675 in
                                uu____7618 :: uu____7640 in
                              uu____7583 :: uu____7609 in
                            uu____7548 :: uu____7574 in
                          uu____7513 :: uu____7539 in
                        uu____7478 :: uu____7504 in
                      uu____7443 :: uu____7469 in
                    uu____7412 :: uu____7434 in
                  uu____7382 :: uu____7403 in
                let mk1 l v1 =
                  let uu____8003 =
                    let uu____8008 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8040  ->
                              match uu____8040 with
                              | (l',uu____8049) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8008
                      (FStar_Option.map
                         (fun uu____8082  ->
                            match uu____8082 with | (uu____8093,b) -> b v1)) in
                  FStar_All.pipe_right uu____8003 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8134  ->
                          match uu____8134 with
                          | (l',uu____8143) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8169 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8169 with
        | (xxsym,xx) ->
            let uu____8174 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8174 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8182 =
                   let uu____8186 =
                     let uu____8187 =
                       let uu____8193 =
                         let uu____8194 =
                           let uu____8197 =
                             let uu____8198 =
                               let uu____8201 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8201) in
                             FStar_SMTEncoding_Util.mkEq uu____8198 in
                           (xx_has_type, uu____8197) in
                         FStar_SMTEncoding_Util.mkImp uu____8194 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8193) in
                     FStar_SMTEncoding_Util.mkForall uu____8187 in
                   let uu____8214 =
                     let uu____8215 =
                       let uu____8216 =
                         let uu____8217 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8217 in
                       Prims.strcat module_name uu____8216 in
                     varops.mk_unique uu____8215 in
                   (uu____8186, (Some "pretyping"), uu____8214) in
                 FStar_SMTEncoding_Util.mkAssume uu____8182)
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
    let uu____8247 =
      let uu____8248 =
        let uu____8252 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8252, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8248 in
    let uu____8254 =
      let uu____8256 =
        let uu____8257 =
          let uu____8261 =
            let uu____8262 =
              let uu____8268 =
                let uu____8269 =
                  let uu____8272 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8272) in
                FStar_SMTEncoding_Util.mkImp uu____8269 in
              ([[typing_pred]], [xx], uu____8268) in
            mkForall_fuel uu____8262 in
          (uu____8261, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8257 in
      [uu____8256] in
    uu____8247 :: uu____8254 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8300 =
      let uu____8301 =
        let uu____8305 =
          let uu____8306 =
            let uu____8312 =
              let uu____8315 =
                let uu____8317 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8317] in
              [uu____8315] in
            let uu____8320 =
              let uu____8321 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8321 tt in
            (uu____8312, [bb], uu____8320) in
          FStar_SMTEncoding_Util.mkForall uu____8306 in
        (uu____8305, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8301 in
    let uu____8332 =
      let uu____8334 =
        let uu____8335 =
          let uu____8339 =
            let uu____8340 =
              let uu____8346 =
                let uu____8347 =
                  let uu____8350 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8350) in
                FStar_SMTEncoding_Util.mkImp uu____8347 in
              ([[typing_pred]], [xx], uu____8346) in
            mkForall_fuel uu____8340 in
          (uu____8339, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8335 in
      [uu____8334] in
    uu____8300 :: uu____8332 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8384 =
        let uu____8385 =
          let uu____8389 =
            let uu____8391 =
              let uu____8393 =
                let uu____8395 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8396 =
                  let uu____8398 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8398] in
                uu____8395 :: uu____8396 in
              tt :: uu____8393 in
            tt :: uu____8391 in
          ("Prims.Precedes", uu____8389) in
        FStar_SMTEncoding_Util.mkApp uu____8385 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8384 in
    let precedes_y_x =
      let uu____8401 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8401 in
    let uu____8403 =
      let uu____8404 =
        let uu____8408 =
          let uu____8409 =
            let uu____8415 =
              let uu____8418 =
                let uu____8420 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8420] in
              [uu____8418] in
            let uu____8423 =
              let uu____8424 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8424 tt in
            (uu____8415, [bb], uu____8423) in
          FStar_SMTEncoding_Util.mkForall uu____8409 in
        (uu____8408, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8404 in
    let uu____8435 =
      let uu____8437 =
        let uu____8438 =
          let uu____8442 =
            let uu____8443 =
              let uu____8449 =
                let uu____8450 =
                  let uu____8453 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8453) in
                FStar_SMTEncoding_Util.mkImp uu____8450 in
              ([[typing_pred]], [xx], uu____8449) in
            mkForall_fuel uu____8443 in
          (uu____8442, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8438 in
      let uu____8466 =
        let uu____8468 =
          let uu____8469 =
            let uu____8473 =
              let uu____8474 =
                let uu____8480 =
                  let uu____8481 =
                    let uu____8484 =
                      let uu____8485 =
                        let uu____8487 =
                          let uu____8489 =
                            let uu____8491 =
                              let uu____8492 =
                                let uu____8495 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8496 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8495, uu____8496) in
                              FStar_SMTEncoding_Util.mkGT uu____8492 in
                            let uu____8497 =
                              let uu____8499 =
                                let uu____8500 =
                                  let uu____8503 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8504 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8503, uu____8504) in
                                FStar_SMTEncoding_Util.mkGTE uu____8500 in
                              let uu____8505 =
                                let uu____8507 =
                                  let uu____8508 =
                                    let uu____8511 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8512 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8511, uu____8512) in
                                  FStar_SMTEncoding_Util.mkLT uu____8508 in
                                [uu____8507] in
                              uu____8499 :: uu____8505 in
                            uu____8491 :: uu____8497 in
                          typing_pred_y :: uu____8489 in
                        typing_pred :: uu____8487 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8485 in
                    (uu____8484, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8481 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8480) in
              mkForall_fuel uu____8474 in
            (uu____8473, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8469 in
        [uu____8468] in
      uu____8437 :: uu____8466 in
    uu____8403 :: uu____8435 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8542 =
      let uu____8543 =
        let uu____8547 =
          let uu____8548 =
            let uu____8554 =
              let uu____8557 =
                let uu____8559 = FStar_SMTEncoding_Term.boxString b in
                [uu____8559] in
              [uu____8557] in
            let uu____8562 =
              let uu____8563 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8563 tt in
            (uu____8554, [bb], uu____8562) in
          FStar_SMTEncoding_Util.mkForall uu____8548 in
        (uu____8547, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8543 in
    let uu____8574 =
      let uu____8576 =
        let uu____8577 =
          let uu____8581 =
            let uu____8582 =
              let uu____8588 =
                let uu____8589 =
                  let uu____8592 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8592) in
                FStar_SMTEncoding_Util.mkImp uu____8589 in
              ([[typing_pred]], [xx], uu____8588) in
            mkForall_fuel uu____8582 in
          (uu____8581, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8577 in
      [uu____8576] in
    uu____8542 :: uu____8574 in
  let mk_ref1 env reft_name uu____8614 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8625 =
        let uu____8629 =
          let uu____8631 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8631] in
        (reft_name, uu____8629) in
      FStar_SMTEncoding_Util.mkApp uu____8625 in
    let refb =
      let uu____8634 =
        let uu____8638 =
          let uu____8640 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8640] in
        (reft_name, uu____8638) in
      FStar_SMTEncoding_Util.mkApp uu____8634 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8644 =
      let uu____8645 =
        let uu____8649 =
          let uu____8650 =
            let uu____8656 =
              let uu____8657 =
                let uu____8660 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8660) in
              FStar_SMTEncoding_Util.mkImp uu____8657 in
            ([[typing_pred]], [xx; aa], uu____8656) in
          mkForall_fuel uu____8650 in
        (uu____8649, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8645 in
    [uu____8644] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8700 =
      let uu____8701 =
        let uu____8705 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8705, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8701 in
    [uu____8700] in
  let mk_and_interp env conj uu____8716 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8733 =
      let uu____8734 =
        let uu____8738 =
          let uu____8739 =
            let uu____8745 =
              let uu____8746 =
                let uu____8749 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8749, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8746 in
            ([[l_and_a_b]], [aa; bb], uu____8745) in
          FStar_SMTEncoding_Util.mkForall uu____8739 in
        (uu____8738, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8734 in
    [uu____8733] in
  let mk_or_interp env disj uu____8773 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8790 =
      let uu____8791 =
        let uu____8795 =
          let uu____8796 =
            let uu____8802 =
              let uu____8803 =
                let uu____8806 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8806, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8803 in
            ([[l_or_a_b]], [aa; bb], uu____8802) in
          FStar_SMTEncoding_Util.mkForall uu____8796 in
        (uu____8795, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8791 in
    [uu____8790] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____8847 =
      let uu____8848 =
        let uu____8852 =
          let uu____8853 =
            let uu____8859 =
              let uu____8860 =
                let uu____8863 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8863, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8860 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____8859) in
          FStar_SMTEncoding_Util.mkForall uu____8853 in
        (uu____8852, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8848 in
    [uu____8847] in
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
    let uu____8910 =
      let uu____8911 =
        let uu____8915 =
          let uu____8916 =
            let uu____8922 =
              let uu____8923 =
                let uu____8926 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8926, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8923 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____8922) in
          FStar_SMTEncoding_Util.mkForall uu____8916 in
        (uu____8915, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8911 in
    [uu____8910] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8971 =
      let uu____8972 =
        let uu____8976 =
          let uu____8977 =
            let uu____8983 =
              let uu____8984 =
                let uu____8987 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____8987, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8984 in
            ([[l_imp_a_b]], [aa; bb], uu____8983) in
          FStar_SMTEncoding_Util.mkForall uu____8977 in
        (uu____8976, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8972 in
    [uu____8971] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9028 =
      let uu____9029 =
        let uu____9033 =
          let uu____9034 =
            let uu____9040 =
              let uu____9041 =
                let uu____9044 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9044, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9041 in
            ([[l_iff_a_b]], [aa; bb], uu____9040) in
          FStar_SMTEncoding_Util.mkForall uu____9034 in
        (uu____9033, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9029 in
    [uu____9028] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9078 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9078 in
    let uu____9080 =
      let uu____9081 =
        let uu____9085 =
          let uu____9086 =
            let uu____9092 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9092) in
          FStar_SMTEncoding_Util.mkForall uu____9086 in
        (uu____9085, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9081 in
    [uu____9080] in
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
      let uu____9132 =
        let uu____9136 =
          let uu____9138 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9138] in
        ("Valid", uu____9136) in
      FStar_SMTEncoding_Util.mkApp uu____9132 in
    let uu____9140 =
      let uu____9141 =
        let uu____9145 =
          let uu____9146 =
            let uu____9152 =
              let uu____9153 =
                let uu____9156 =
                  let uu____9157 =
                    let uu____9163 =
                      let uu____9166 =
                        let uu____9168 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9168] in
                      [uu____9166] in
                    let uu____9171 =
                      let uu____9172 =
                        let uu____9175 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9175, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9172 in
                    (uu____9163, [xx1], uu____9171) in
                  FStar_SMTEncoding_Util.mkForall uu____9157 in
                (uu____9156, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9153 in
            ([[l_forall_a_b]], [aa; bb], uu____9152) in
          FStar_SMTEncoding_Util.mkForall uu____9146 in
        (uu____9145, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9141 in
    [uu____9140] in
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
      let uu____9226 =
        let uu____9230 =
          let uu____9232 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9232] in
        ("Valid", uu____9230) in
      FStar_SMTEncoding_Util.mkApp uu____9226 in
    let uu____9234 =
      let uu____9235 =
        let uu____9239 =
          let uu____9240 =
            let uu____9246 =
              let uu____9247 =
                let uu____9250 =
                  let uu____9251 =
                    let uu____9257 =
                      let uu____9260 =
                        let uu____9262 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9262] in
                      [uu____9260] in
                    let uu____9265 =
                      let uu____9266 =
                        let uu____9269 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9269, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9266 in
                    (uu____9257, [xx1], uu____9265) in
                  FStar_SMTEncoding_Util.mkExists uu____9251 in
                (uu____9250, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9247 in
            ([[l_exists_a_b]], [aa; bb], uu____9246) in
          FStar_SMTEncoding_Util.mkForall uu____9240 in
        (uu____9239, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9235 in
    [uu____9234] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9305 =
      let uu____9306 =
        let uu____9310 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9311 = varops.mk_unique "typing_range_const" in
        (uu____9310, (Some "Range_const typing"), uu____9311) in
      FStar_SMTEncoding_Util.mkAssume uu____9306 in
    [uu____9305] in
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
          let uu____9573 =
            FStar_Util.find_opt
              (fun uu____9591  ->
                 match uu____9591 with
                 | (l,uu____9601) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9573 with
          | None  -> []
          | Some (uu____9623,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9660 = encode_function_type_as_formula t env in
        match uu____9660 with
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
            let uu____9692 =
              (let uu____9693 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9693) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9692
            then
              let uu____9697 = new_term_constant_and_tok_from_lid env lid in
              match uu____9697 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9709 =
                      let uu____9710 = FStar_Syntax_Subst.compress t_norm in
                      uu____9710.FStar_Syntax_Syntax.n in
                    match uu____9709 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9715) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9732  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9735 -> [] in
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
              (let uu____9744 = prims.is lid in
               if uu____9744
               then
                 let vname = varops.new_fvar lid in
                 let uu____9749 = prims.mk lid vname in
                 match uu____9749 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9764 =
                    let uu____9770 = curried_arrow_formals_comp t_norm in
                    match uu____9770 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9781 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9781
                          then
                            let uu____9782 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___145_9783 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___145_9783.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___145_9783.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___145_9783.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___145_9783.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___145_9783.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___145_9783.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___145_9783.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___145_9783.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___145_9783.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___145_9783.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___145_9783.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___145_9783.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___145_9783.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___145_9783.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___145_9783.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___145_9783.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___145_9783.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___145_9783.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___145_9783.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___145_9783.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___145_9783.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___145_9783.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___145_9783.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___145_9783.FStar_TypeChecker_Env.proof_ns)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9782
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9790 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9790)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9764 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9817 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____9817 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9830 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___116_9854  ->
                                     match uu___116_9854 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9857 =
                                           FStar_Util.prefix vars in
                                         (match uu____9857 with
                                          | (uu____9868,(xxsym,uu____9870))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____9880 =
                                                let uu____9881 =
                                                  let uu____9885 =
                                                    let uu____9886 =
                                                      let uu____9892 =
                                                        let uu____9893 =
                                                          let uu____9896 =
                                                            let uu____9897 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____9897 in
                                                          (vapp, uu____9896) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9893 in
                                                      ([[vapp]], vars,
                                                        uu____9892) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9886 in
                                                  (uu____9885,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9881 in
                                              [uu____9880])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____9908 =
                                           FStar_Util.prefix vars in
                                         (match uu____9908 with
                                          | (uu____9919,(xxsym,uu____9921))
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
                                              let uu____9935 =
                                                let uu____9936 =
                                                  let uu____9940 =
                                                    let uu____9941 =
                                                      let uu____9947 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____9947) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9941 in
                                                  (uu____9940,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9936 in
                                              [uu____9935])
                                     | uu____9956 -> [])) in
                           let uu____9957 = encode_binders None formals env1 in
                           (match uu____9957 with
                            | (vars,guards,env',decls1,uu____9973) ->
                                let uu____9980 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____9985 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____9985, decls1)
                                  | Some p ->
                                      let uu____9987 = encode_formula p env' in
                                      (match uu____9987 with
                                       | (g,ds) ->
                                           let uu____9994 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____9994,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____9980 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10003 =
                                         let uu____10007 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10007) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10003 in
                                     let uu____10012 =
                                       let vname_decl =
                                         let uu____10017 =
                                           let uu____10023 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10028  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10023,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10017 in
                                       let uu____10033 =
                                         let env2 =
                                           let uu___146_10037 = env1 in
                                           {
                                             bindings =
                                               (uu___146_10037.bindings);
                                             depth = (uu___146_10037.depth);
                                             tcenv = (uu___146_10037.tcenv);
                                             warn = (uu___146_10037.warn);
                                             cache = (uu___146_10037.cache);
                                             nolabels =
                                               (uu___146_10037.nolabels);
                                             use_zfuel_name =
                                               (uu___146_10037.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___146_10037.current_module_name)
                                           } in
                                         let uu____10038 =
                                           let uu____10039 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10039 in
                                         if uu____10038
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10033 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10049::uu____10050 ->
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
                                                   let uu____10073 =
                                                     let uu____10079 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10079) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10073 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10093 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10095 =
                                             match formals with
                                             | [] ->
                                                 let uu____10104 =
                                                   let uu____10105 =
                                                     let uu____10107 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10107 in
                                                   push_free_var env1 lid
                                                     vname uu____10105 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10104)
                                             | uu____10110 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10115 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10115 in
                                                 let name_tok_corr =
                                                   let uu____10117 =
                                                     let uu____10121 =
                                                       let uu____10122 =
                                                         let uu____10128 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10128) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10122 in
                                                     (uu____10121,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10117 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10095 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10012 with
                                      | (decls2,env2) ->
                                          let uu____10152 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10157 =
                                              encode_term res_t1 env' in
                                            match uu____10157 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10165 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10165,
                                                  decls) in
                                          (match uu____10152 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10173 =
                                                   let uu____10177 =
                                                     let uu____10178 =
                                                       let uu____10184 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10184) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10178 in
                                                   (uu____10177,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10173 in
                                               let freshness =
                                                 let uu____10193 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10193
                                                 then
                                                   let uu____10196 =
                                                     let uu____10197 =
                                                       let uu____10203 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10209 =
                                                         varops.next_id () in
                                                       (vname, uu____10203,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10209) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10197 in
                                                   let uu____10211 =
                                                     let uu____10213 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10213] in
                                                   uu____10196 :: uu____10211
                                                 else [] in
                                               let g =
                                                 let uu____10217 =
                                                   let uu____10219 =
                                                     let uu____10221 =
                                                       let uu____10223 =
                                                         let uu____10225 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10225 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10223 in
                                                     FStar_List.append decls3
                                                       uu____10221 in
                                                   FStar_List.append decls2
                                                     uu____10219 in
                                                 FStar_List.append decls11
                                                   uu____10217 in
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
          let uu____10247 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10247 with
          | None  ->
              let uu____10270 = encode_free_var env x t t_norm [] in
              (match uu____10270 with
               | (decls,env1) ->
                   let uu____10285 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10285 with
                    | (n1,x',uu____10304) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10316) -> ((n1, x1), [], env)
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
          let uu____10349 = encode_free_var env lid t tt quals in
          match uu____10349 with
          | (decls,env1) ->
              let uu____10360 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10360
              then
                let uu____10364 =
                  let uu____10366 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10366 in
                (uu____10364, env1)
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
             (fun uu____10394  ->
                fun lb  ->
                  match uu____10394 with
                  | (decls,env1) ->
                      let uu____10406 =
                        let uu____10410 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10410
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10406 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10424 = FStar_Syntax_Util.head_and_args t in
    match uu____10424 with
    | (hd1,args) ->
        let uu____10450 =
          let uu____10451 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10451.FStar_Syntax_Syntax.n in
        (match uu____10450 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10455,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10468 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10483  ->
      fun quals  ->
        match uu____10483 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10532 = FStar_Util.first_N nbinders formals in
              match uu____10532 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10572  ->
                         fun uu____10573  ->
                           match (uu____10572, uu____10573) with
                           | ((formal,uu____10583),(binder,uu____10585)) ->
                               let uu____10590 =
                                 let uu____10595 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10595) in
                               FStar_Syntax_Syntax.NT uu____10590) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10600 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10614  ->
                              match uu____10614 with
                              | (x,i) ->
                                  let uu____10621 =
                                    let uu___147_10622 = x in
                                    let uu____10623 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___147_10622.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___147_10622.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10623
                                    } in
                                  (uu____10621, i))) in
                    FStar_All.pipe_right uu____10600
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10635 =
                      let uu____10637 =
                        let uu____10638 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10638.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10637 in
                    let uu____10642 =
                      let uu____10643 = FStar_Syntax_Subst.compress body in
                      let uu____10644 =
                        let uu____10645 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10645 in
                      FStar_Syntax_Syntax.extend_app_n uu____10643
                        uu____10644 in
                    uu____10642 uu____10635 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10687 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10687
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___148_10688 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___148_10688.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___148_10688.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___148_10688.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___148_10688.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___148_10688.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___148_10688.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___148_10688.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___148_10688.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___148_10688.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___148_10688.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___148_10688.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___148_10688.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___148_10688.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___148_10688.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___148_10688.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___148_10688.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___148_10688.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___148_10688.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___148_10688.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___148_10688.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___148_10688.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___148_10688.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___148_10688.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___148_10688.FStar_TypeChecker_Env.proof_ns)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10709 = FStar_Syntax_Util.abs_formals e in
                match uu____10709 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10758::uu____10759 ->
                         let uu____10767 =
                           let uu____10768 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10768.FStar_Syntax_Syntax.n in
                         (match uu____10767 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10795 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10795 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10821 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10821
                                   then
                                     let uu____10839 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____10839 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____10885  ->
                                                   fun uu____10886  ->
                                                     match (uu____10885,
                                                             uu____10886)
                                                     with
                                                     | ((x,uu____10896),
                                                        (b,uu____10898)) ->
                                                         let uu____10903 =
                                                           let uu____10908 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____10908) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____10903)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____10910 =
                                            let uu____10921 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____10921) in
                                          (uu____10910, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____10956 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____10956 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11008) ->
                              let uu____11013 =
                                let uu____11024 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11024 in
                              (uu____11013, true)
                          | uu____11057 when Prims.op_Negation norm1 ->
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
                          | uu____11059 ->
                              let uu____11060 =
                                let uu____11061 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11062 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11061
                                  uu____11062 in
                              failwith uu____11060)
                     | uu____11075 ->
                         let uu____11076 =
                           let uu____11077 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11077.FStar_Syntax_Syntax.n in
                         (match uu____11076 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11104 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11104 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11122 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11122 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11170 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11198 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11198
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11205 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11246  ->
                            fun lb  ->
                              match uu____11246 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11297 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11297
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11300 =
                                      let uu____11308 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11308
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11300 with
                                    | (tok,decl,env2) ->
                                        let uu____11333 =
                                          let uu____11340 =
                                            let uu____11346 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11346, tok) in
                                          uu____11340 :: toks in
                                        (uu____11333, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11205 with
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
                        | uu____11448 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11453 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11453 vars)
                            else
                              (let uu____11455 =
                                 let uu____11459 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11459) in
                               FStar_SMTEncoding_Util.mkApp uu____11455) in
                      let uu____11464 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___117_11466  ->
                                 match uu___117_11466 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11467 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11470 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11470))) in
                      if uu____11464
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11490;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11492;
                                FStar_Syntax_Syntax.lbeff = uu____11493;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11534 =
                                 let uu____11538 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11538 with
                                 | (tcenv',uu____11549,e_t) ->
                                     let uu____11553 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11560 -> failwith "Impossible" in
                                     (match uu____11553 with
                                      | (e1,t_norm1) ->
                                          ((let uu___151_11569 = env1 in
                                            {
                                              bindings =
                                                (uu___151_11569.bindings);
                                              depth = (uu___151_11569.depth);
                                              tcenv = tcenv';
                                              warn = (uu___151_11569.warn);
                                              cache = (uu___151_11569.cache);
                                              nolabels =
                                                (uu___151_11569.nolabels);
                                              use_zfuel_name =
                                                (uu___151_11569.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___151_11569.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___151_11569.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11534 with
                                | (env',e1,t_norm1) ->
                                    let uu____11576 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11576 with
                                     | ((binders,body,uu____11588,uu____11589),curry)
                                         ->
                                         ((let uu____11596 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11596
                                           then
                                             let uu____11597 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11598 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11597 uu____11598
                                           else ());
                                          (let uu____11600 =
                                             encode_binders None binders env' in
                                           match uu____11600 with
                                           | (vars,guards,env'1,binder_decls,uu____11616)
                                               ->
                                               let body1 =
                                                 let uu____11624 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11624
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11627 =
                                                 let uu____11632 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11632
                                                 then
                                                   let uu____11638 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11639 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11638, uu____11639)
                                                 else
                                                   (let uu____11645 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11645)) in
                                               (match uu____11627 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11659 =
                                                        let uu____11663 =
                                                          let uu____11664 =
                                                            let uu____11670 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11670) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11664 in
                                                        let uu____11676 =
                                                          let uu____11678 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11678 in
                                                        (uu____11663,
                                                          uu____11676,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11659 in
                                                    let uu____11680 =
                                                      let uu____11682 =
                                                        let uu____11684 =
                                                          let uu____11686 =
                                                            let uu____11688 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11688 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11686 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11684 in
                                                      FStar_List.append
                                                        decls1 uu____11682 in
                                                    (uu____11680, env1))))))
                           | uu____11691 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11710 = varops.fresh "fuel" in
                             (uu____11710, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11713 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11752  ->
                                     fun uu____11753  ->
                                       match (uu____11752, uu____11753) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____11835 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____11835 in
                                           let gtok =
                                             let uu____11837 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____11837 in
                                           let env3 =
                                             let uu____11839 =
                                               let uu____11841 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____11841 in
                                             push_free_var env2 flid gtok
                                               uu____11839 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11713 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____11927
                                 t_norm uu____11929 =
                                 match (uu____11927, uu____11929) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____11956;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____11957;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____11974 =
                                       let uu____11978 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____11978 with
                                       | (tcenv',uu____11993,e_t) ->
                                           let uu____11997 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12004 ->
                                                 failwith "Impossible" in
                                           (match uu____11997 with
                                            | (e1,t_norm1) ->
                                                ((let uu___152_12013 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___152_12013.bindings);
                                                    depth =
                                                      (uu___152_12013.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___152_12013.warn);
                                                    cache =
                                                      (uu___152_12013.cache);
                                                    nolabels =
                                                      (uu___152_12013.nolabels);
                                                    use_zfuel_name =
                                                      (uu___152_12013.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___152_12013.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___152_12013.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____11974 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12023 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12023
                                            then
                                              let uu____12024 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12025 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12026 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12024 uu____12025
                                                uu____12026
                                            else ());
                                           (let uu____12028 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12028 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12050 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12050
                                                  then
                                                    let uu____12051 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12052 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12053 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12054 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12051 uu____12052
                                                      uu____12053 uu____12054
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12058 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12058 with
                                                  | (vars,guards,env'1,binder_decls,uu____12076)
                                                      ->
                                                      let decl_g =
                                                        let uu____12084 =
                                                          let uu____12090 =
                                                            let uu____12092 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12092 in
                                                          (g, uu____12090,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12084 in
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
                                                        let uu____12107 =
                                                          let uu____12111 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12111) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12107 in
                                                      let gsapp =
                                                        let uu____12117 =
                                                          let uu____12121 =
                                                            let uu____12123 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12123 ::
                                                              vars_tm in
                                                          (g, uu____12121) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12117 in
                                                      let gmax =
                                                        let uu____12127 =
                                                          let uu____12131 =
                                                            let uu____12133 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12133 ::
                                                              vars_tm in
                                                          (g, uu____12131) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12127 in
                                                      let body1 =
                                                        let uu____12137 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12137
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12139 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12139 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12150
                                                               =
                                                               let uu____12154
                                                                 =
                                                                 let uu____12155
                                                                   =
                                                                   let uu____12163
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
                                                                    uu____12163) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12155 in
                                                               let uu____12174
                                                                 =
                                                                 let uu____12176
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12176 in
                                                               (uu____12154,
                                                                 uu____12174,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12150 in
                                                           let eqn_f =
                                                             let uu____12179
                                                               =
                                                               let uu____12183
                                                                 =
                                                                 let uu____12184
                                                                   =
                                                                   let uu____12190
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12190) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12184 in
                                                               (uu____12183,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12179 in
                                                           let eqn_g' =
                                                             let uu____12198
                                                               =
                                                               let uu____12202
                                                                 =
                                                                 let uu____12203
                                                                   =
                                                                   let uu____12209
                                                                    =
                                                                    let uu____12210
                                                                    =
                                                                    let uu____12213
                                                                    =
                                                                    let uu____12214
                                                                    =
                                                                    let uu____12218
                                                                    =
                                                                    let uu____12220
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12220
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12218) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12214 in
                                                                    (gsapp,
                                                                    uu____12213) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12210 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12209) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12203 in
                                                               (uu____12202,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12198 in
                                                           let uu____12232 =
                                                             let uu____12237
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12237
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12254)
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
                                                                    let uu____12269
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12269
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12272
                                                                    =
                                                                    let uu____12276
                                                                    =
                                                                    let uu____12277
                                                                    =
                                                                    let uu____12283
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12283) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12277 in
                                                                    (uu____12276,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12272 in
                                                                 let uu____12294
                                                                   =
                                                                   let uu____12298
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12298
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12306
                                                                    =
                                                                    let uu____12308
                                                                    =
                                                                    let uu____12309
                                                                    =
                                                                    let uu____12313
                                                                    =
                                                                    let uu____12314
                                                                    =
                                                                    let uu____12320
                                                                    =
                                                                    let uu____12321
                                                                    =
                                                                    let uu____12324
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12324,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12321 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12320) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12314 in
                                                                    (uu____12313,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12309 in
                                                                    [uu____12308] in
                                                                    (d3,
                                                                    uu____12306) in
                                                                 (match uu____12294
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12232
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
                               let uu____12359 =
                                 let uu____12366 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12402  ->
                                      fun uu____12403  ->
                                        match (uu____12402, uu____12403) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12489 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12489 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12366 in
                               (match uu____12359 with
                                | (decls2,eqns,env01) ->
                                    let uu____12529 =
                                      let isDeclFun uu___118_12537 =
                                        match uu___118_12537 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12538 -> true
                                        | uu____12544 -> false in
                                      let uu____12545 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12545
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12529 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12572 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12572
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
        let uu____12605 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12605 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12608 = encode_sigelt' env se in
      match uu____12608 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12618 =
                  let uu____12619 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12619 in
                [uu____12618]
            | uu____12620 ->
                let uu____12621 =
                  let uu____12623 =
                    let uu____12624 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12624 in
                  uu____12623 :: g in
                let uu____12625 =
                  let uu____12627 =
                    let uu____12628 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12628 in
                  [uu____12627] in
                FStar_List.append uu____12621 uu____12625 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12636 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12645 =
            let uu____12646 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12646 Prims.op_Negation in
          if uu____12645
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12666 ->
                   let uu____12667 =
                     let uu____12670 =
                       let uu____12671 =
                         let uu____12686 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12686) in
                       FStar_Syntax_Syntax.Tm_abs uu____12671 in
                     FStar_Syntax_Syntax.mk uu____12670 in
                   uu____12667 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12739 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12739 with
               | (aname,atok,env2) ->
                   let uu____12749 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12749 with
                    | (formals,uu____12759) ->
                        let uu____12766 =
                          let uu____12769 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12769 env2 in
                        (match uu____12766 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12777 =
                                 let uu____12778 =
                                   let uu____12784 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12792  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12784,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12778 in
                               [uu____12777;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12799 =
                               let aux uu____12828 uu____12829 =
                                 match (uu____12828, uu____12829) with
                                 | ((bv,uu____12856),(env3,acc_sorts,acc)) ->
                                     let uu____12877 = gen_term_var env3 bv in
                                     (match uu____12877 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12799 with
                              | (uu____12915,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____12929 =
                                      let uu____12933 =
                                        let uu____12934 =
                                          let uu____12940 =
                                            let uu____12941 =
                                              let uu____12944 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____12944) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____12941 in
                                          ([[app]], xs_sorts, uu____12940) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12934 in
                                      (uu____12933, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12929 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____12956 =
                                      let uu____12960 =
                                        let uu____12961 =
                                          let uu____12967 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____12967) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____12961 in
                                      (uu____12960,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____12956 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____12977 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____12977 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____12993,uu____12994)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____12995 = new_term_constant_and_tok_from_lid env lid in
          (match uu____12995 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13006,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13011 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___119_13013  ->
                      match uu___119_13013 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13016 -> false)) in
            Prims.op_Negation uu____13011 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13022 = encode_top_level_val env fv t quals in
             match uu____13022 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13034 =
                   let uu____13036 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13036 in
                 (uu____13034, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13041 = encode_formula f env in
          (match uu____13041 with
           | (f1,decls) ->
               let g =
                 let uu____13050 =
                   let uu____13051 =
                     let uu____13055 =
                       let uu____13057 =
                         let uu____13058 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13058 in
                       Some uu____13057 in
                     let uu____13059 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13055, uu____13059) in
                   FStar_SMTEncoding_Util.mkAssume uu____13051 in
                 [uu____13050] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13063,uu____13064) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13070 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13077 =
                       let uu____13082 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13082.FStar_Syntax_Syntax.fv_name in
                     uu____13077.FStar_Syntax_Syntax.v in
                   let uu____13086 =
                     let uu____13087 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13087 in
                   if uu____13086
                   then
                     let val_decl =
                       let uu___153_13102 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___153_13102.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___153_13102.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___153_13102.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13106 = encode_sigelt' env1 val_decl in
                     match uu____13106 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13070 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13123,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13125;
                          FStar_Syntax_Syntax.lbtyp = uu____13126;
                          FStar_Syntax_Syntax.lbeff = uu____13127;
                          FStar_Syntax_Syntax.lbdef = uu____13128;_}::[]),uu____13129,uu____13130)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13144 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13144 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13167 =
                   let uu____13169 =
                     let uu____13170 =
                       let uu____13174 =
                         let uu____13175 =
                           let uu____13181 =
                             let uu____13182 =
                               let uu____13185 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13185) in
                             FStar_SMTEncoding_Util.mkEq uu____13182 in
                           ([[b2t_x]], [xx], uu____13181) in
                         FStar_SMTEncoding_Util.mkForall uu____13175 in
                       (uu____13174, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13170 in
                   [uu____13169] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13167 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13202,uu____13203,uu____13204)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___120_13210  ->
                  match uu___120_13210 with
                  | FStar_Syntax_Syntax.Discriminator uu____13211 -> true
                  | uu____13212 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13214,lids,uu____13216) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13223 =
                     let uu____13224 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13224.FStar_Ident.idText in
                   uu____13223 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___121_13226  ->
                     match uu___121_13226 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13227 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13230,uu____13231)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___122_13241  ->
                  match uu___122_13241 with
                  | FStar_Syntax_Syntax.Projector uu____13242 -> true
                  | uu____13245 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13252 = try_lookup_free_var env l in
          (match uu____13252 with
           | Some uu____13256 -> ([], env)
           | None  ->
               let se1 =
                 let uu___154_13259 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___154_13259.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___154_13259.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13265,uu____13266) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13278) ->
          let uu____13283 = encode_sigelts env ses in
          (match uu____13283 with
           | (g,env1) ->
               let uu____13293 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___123_13303  ->
                         match uu___123_13303 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13304;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13305;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13306;_}
                             -> false
                         | uu____13308 -> true)) in
               (match uu____13293 with
                | (g',inversions) ->
                    let uu____13317 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___124_13327  ->
                              match uu___124_13327 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13328 ->
                                  true
                              | uu____13334 -> false)) in
                    (match uu____13317 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13345,tps,k,uu____13348,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___125_13358  ->
                    match uu___125_13358 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13359 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13366 = c in
              match uu____13366 with
              | (name,args,uu____13370,uu____13371,uu____13372) ->
                  let uu____13375 =
                    let uu____13376 =
                      let uu____13382 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13389  ->
                                match uu____13389 with
                                | (uu____13393,sort,uu____13395) -> sort)) in
                      (name, uu____13382, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13376 in
                  [uu____13375]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13413 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13416 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13416 FStar_Option.isNone)) in
            if uu____13413
            then []
            else
              (let uu____13433 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13433 with
               | (xxsym,xx) ->
                   let uu____13439 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13450  ->
                             fun l  ->
                               match uu____13450 with
                               | (out,decls) ->
                                   let uu____13462 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13462 with
                                    | (uu____13468,data_t) ->
                                        let uu____13470 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13470 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13499 =
                                                 let uu____13500 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13500.FStar_Syntax_Syntax.n in
                                               match uu____13499 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13508,indices) ->
                                                   indices
                                               | uu____13524 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13536  ->
                                                         match uu____13536
                                                         with
                                                         | (x,uu____13540) ->
                                                             let uu____13541
                                                               =
                                                               let uu____13542
                                                                 =
                                                                 let uu____13546
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13546,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13542 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13541)
                                                    env) in
                                             let uu____13548 =
                                               encode_args indices env1 in
                                             (match uu____13548 with
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
                                                      let uu____13568 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13576
                                                                 =
                                                                 let uu____13579
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13579,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13576)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13568
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13581 =
                                                      let uu____13582 =
                                                        let uu____13585 =
                                                          let uu____13586 =
                                                            let uu____13589 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13589,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13586 in
                                                        (out, uu____13585) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13582 in
                                                    (uu____13581,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13439 with
                    | (data_ax,decls) ->
                        let uu____13597 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13597 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13608 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13608 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13611 =
                                 let uu____13615 =
                                   let uu____13616 =
                                     let uu____13622 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13630 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13622,
                                       uu____13630) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13616 in
                                 let uu____13638 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13615, (Some "inversion axiom"),
                                   uu____13638) in
                               FStar_SMTEncoding_Util.mkAssume uu____13611 in
                             let pattern_guarded_inversion =
                               let uu____13642 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13642
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13650 =
                                   let uu____13651 =
                                     let uu____13655 =
                                       let uu____13656 =
                                         let uu____13662 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13670 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13662, uu____13670) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13656 in
                                     let uu____13678 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13655, (Some "inversion axiom"),
                                       uu____13678) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13651 in
                                 [uu____13650]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13681 =
            let uu____13689 =
              let uu____13690 = FStar_Syntax_Subst.compress k in
              uu____13690.FStar_Syntax_Syntax.n in
            match uu____13689 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13719 -> (tps, k) in
          (match uu____13681 with
           | (formals,res) ->
               let uu____13734 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13734 with
                | (formals1,res1) ->
                    let uu____13741 = encode_binders None formals1 env in
                    (match uu____13741 with
                     | (vars,guards,env',binder_decls,uu____13756) ->
                         let uu____13763 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13763 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13776 =
                                  let uu____13780 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13780) in
                                FStar_SMTEncoding_Util.mkApp uu____13776 in
                              let uu____13785 =
                                let tname_decl =
                                  let uu____13791 =
                                    let uu____13792 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13807  ->
                                              match uu____13807 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13815 = varops.next_id () in
                                    (tname, uu____13792,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13815, false) in
                                  constructor_or_logic_type_decl uu____13791 in
                                let uu____13820 =
                                  match vars with
                                  | [] ->
                                      let uu____13827 =
                                        let uu____13828 =
                                          let uu____13830 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____13830 in
                                        push_free_var env1 t tname
                                          uu____13828 in
                                      ([], uu____13827)
                                  | uu____13834 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13840 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13840 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13849 =
                                          let uu____13853 =
                                            let uu____13854 =
                                              let uu____13862 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13862) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13854 in
                                          (uu____13853,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13849 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13820 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13785 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13885 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____13885 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13899 =
                                               let uu____13900 =
                                                 let uu____13904 =
                                                   let uu____13905 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13905 in
                                                 (uu____13904,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13900 in
                                             [uu____13899]
                                           else [] in
                                         let uu____13908 =
                                           let uu____13910 =
                                             let uu____13912 =
                                               let uu____13913 =
                                                 let uu____13917 =
                                                   let uu____13918 =
                                                     let uu____13924 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____13924) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____13918 in
                                                 (uu____13917, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13913 in
                                             [uu____13912] in
                                           FStar_List.append karr uu____13910 in
                                         FStar_List.append decls1 uu____13908 in
                                   let aux =
                                     let uu____13933 =
                                       let uu____13935 =
                                         inversion_axioms tapp vars in
                                       let uu____13937 =
                                         let uu____13939 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____13939] in
                                       FStar_List.append uu____13935
                                         uu____13937 in
                                     FStar_List.append kindingAx uu____13933 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13944,uu____13945,uu____13946,uu____13947,uu____13948)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____13953,t,uu____13955,n_tps,uu____13957) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____13962 = new_term_constant_and_tok_from_lid env d in
          (match uu____13962 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____13973 = FStar_Syntax_Util.arrow_formals t in
               (match uu____13973 with
                | (formals,t_res) ->
                    let uu____13995 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____13995 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14004 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14004 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14042 =
                                            mk_term_projector_name d x in
                                          (uu____14042,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14044 =
                                  let uu____14054 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14054, true) in
                                FStar_All.pipe_right uu____14044
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
                              let uu____14076 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14076 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14084::uu____14085 ->
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
                                         let uu____14110 =
                                           let uu____14116 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14116) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14110
                                     | uu____14129 -> tok_typing in
                                   let uu____14134 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14134 with
                                    | (vars',guards',env'',decls_formals,uu____14149)
                                        ->
                                        let uu____14156 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14156 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14175 ->
                                                   let uu____14179 =
                                                     let uu____14180 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14180 in
                                                   [uu____14179] in
                                             let encode_elim uu____14187 =
                                               let uu____14188 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14188 with
                                               | (head1,args) ->
                                                   let uu____14217 =
                                                     let uu____14218 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14218.FStar_Syntax_Syntax.n in
                                                   (match uu____14217 with
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
                                                        let uu____14236 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14236
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
                                                                 | uu____14262
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14270
                                                                    =
                                                                    let uu____14271
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14271 in
                                                                    if
                                                                    uu____14270
                                                                    then
                                                                    let uu____14278
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14278]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14280
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14293
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14293
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14315
                                                                    =
                                                                    let uu____14319
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14319 in
                                                                    (match uu____14315
                                                                    with
                                                                    | 
                                                                    (uu____14326,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14332
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14332
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14334
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14334
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
                                                             (match uu____14280
                                                              with
                                                              | (uu____14342,arg_vars,elim_eqns_or_guards,uu____14345)
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
                                                                    let uu____14364
                                                                    =
                                                                    let uu____14368
                                                                    =
                                                                    let uu____14369
                                                                    =
                                                                    let uu____14375
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14381
                                                                    =
                                                                    let uu____14382
                                                                    =
                                                                    let uu____14385
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14385) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14382 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14375,
                                                                    uu____14381) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14369 in
                                                                    (uu____14368,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14364 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14398
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14398,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14400
                                                                    =
                                                                    let uu____14404
                                                                    =
                                                                    let uu____14405
                                                                    =
                                                                    let uu____14411
                                                                    =
                                                                    let uu____14414
                                                                    =
                                                                    let uu____14416
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14416] in
                                                                    [uu____14414] in
                                                                    let uu____14419
                                                                    =
                                                                    let uu____14420
                                                                    =
                                                                    let uu____14423
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14424
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14423,
                                                                    uu____14424) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14420 in
                                                                    (uu____14411,
                                                                    [x],
                                                                    uu____14419) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14405 in
                                                                    let uu____14434
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14404,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14434) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14400
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14439
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
                                                                    (let uu____14454
                                                                    =
                                                                    let uu____14455
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14455
                                                                    dapp1 in
                                                                    [uu____14454]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14439
                                                                    FStar_List.flatten in
                                                                    let uu____14459
                                                                    =
                                                                    let uu____14463
                                                                    =
                                                                    let uu____14464
                                                                    =
                                                                    let uu____14470
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14476
                                                                    =
                                                                    let uu____14477
                                                                    =
                                                                    let uu____14480
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14480) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14477 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14470,
                                                                    uu____14476) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14464 in
                                                                    (uu____14463,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14459) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14490 ->
                                                        ((let uu____14492 =
                                                            let uu____14493 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14494 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14493
                                                              uu____14494 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14492);
                                                         ([], []))) in
                                             let uu____14497 = encode_elim () in
                                             (match uu____14497 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14509 =
                                                      let uu____14511 =
                                                        let uu____14513 =
                                                          let uu____14515 =
                                                            let uu____14517 =
                                                              let uu____14518
                                                                =
                                                                let uu____14524
                                                                  =
                                                                  let uu____14526
                                                                    =
                                                                    let uu____14527
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14527 in
                                                                  Some
                                                                    uu____14526 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14524) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14518 in
                                                            [uu____14517] in
                                                          let uu____14530 =
                                                            let uu____14532 =
                                                              let uu____14534
                                                                =
                                                                let uu____14536
                                                                  =
                                                                  let uu____14538
                                                                    =
                                                                    let uu____14540
                                                                    =
                                                                    let uu____14542
                                                                    =
                                                                    let uu____14543
                                                                    =
                                                                    let uu____14547
                                                                    =
                                                                    let uu____14548
                                                                    =
                                                                    let uu____14554
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14554) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14548 in
                                                                    (uu____14547,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14543 in
                                                                    let uu____14561
                                                                    =
                                                                    let uu____14563
                                                                    =
                                                                    let uu____14564
                                                                    =
                                                                    let uu____14568
                                                                    =
                                                                    let uu____14569
                                                                    =
                                                                    let uu____14575
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14581
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14575,
                                                                    uu____14581) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14569 in
                                                                    (uu____14568,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14564 in
                                                                    [uu____14563] in
                                                                    uu____14542
                                                                    ::
                                                                    uu____14561 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14540 in
                                                                  FStar_List.append
                                                                    uu____14538
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14536 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14534 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14532 in
                                                          FStar_List.append
                                                            uu____14515
                                                            uu____14530 in
                                                        FStar_List.append
                                                          decls3 uu____14513 in
                                                      FStar_List.append
                                                        decls2 uu____14511 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14509 in
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
           (fun uu____14602  ->
              fun se  ->
                match uu____14602 with
                | (g,env1) ->
                    let uu____14614 = encode_sigelt env1 se in
                    (match uu____14614 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14650 =
        match uu____14650 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14668 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14673 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14673
                   then
                     let uu____14674 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14675 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14676 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14674 uu____14675 uu____14676
                   else ());
                  (let uu____14678 = encode_term t1 env1 in
                   match uu____14678 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14688 =
                         let uu____14692 =
                           let uu____14693 =
                             let uu____14694 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14694
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14693 in
                         new_term_constant_from_string env1 x uu____14692 in
                       (match uu____14688 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14705 = FStar_Options.log_queries () in
                              if uu____14705
                              then
                                let uu____14707 =
                                  let uu____14708 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14709 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14710 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14708 uu____14709 uu____14710 in
                                Some uu____14707
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14721,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14730 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14730 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14749 = encode_sigelt env1 se in
                 (match uu____14749 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14759 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14759 with | (uu____14771,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14816  ->
            match uu____14816 with
            | (l,uu____14823,uu____14824) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14845  ->
            match uu____14845 with
            | (l,uu____14853,uu____14854) ->
                let uu____14859 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39)
                    (Prims.fst l) in
                let uu____14860 =
                  let uu____14862 =
                    let uu____14863 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14863 in
                  [uu____14862] in
                uu____14859 :: uu____14860)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14874 =
      let uu____14876 =
        let uu____14877 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____14879 =
          let uu____14880 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____14880 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14877;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____14879
        } in
      [uu____14876] in
    FStar_ST.write last_env uu____14874
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____14890 = FStar_ST.read last_env in
      match uu____14890 with
      | [] -> failwith "No env; call init first!"
      | e::uu____14896 ->
          let uu___155_14898 = e in
          let uu____14899 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___155_14898.bindings);
            depth = (uu___155_14898.depth);
            tcenv;
            warn = (uu___155_14898.warn);
            cache = (uu___155_14898.cache);
            nolabels = (uu___155_14898.nolabels);
            use_zfuel_name = (uu___155_14898.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_14898.encode_non_total_function_typ);
            current_module_name = uu____14899
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____14903 = FStar_ST.read last_env in
    match uu____14903 with
    | [] -> failwith "Empty env stack"
    | uu____14908::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____14916  ->
    let uu____14917 = FStar_ST.read last_env in
    match uu____14917 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___156_14928 = hd1 in
          {
            bindings = (uu___156_14928.bindings);
            depth = (uu___156_14928.depth);
            tcenv = (uu___156_14928.tcenv);
            warn = (uu___156_14928.warn);
            cache = refs;
            nolabels = (uu___156_14928.nolabels);
            use_zfuel_name = (uu___156_14928.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___156_14928.encode_non_total_function_typ);
            current_module_name = (uu___156_14928.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____14934  ->
    let uu____14935 = FStar_ST.read last_env in
    match uu____14935 with
    | [] -> failwith "Popping an empty stack"
    | uu____14940::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____14948  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____14951  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____14954  ->
    let uu____14955 = FStar_ST.read last_env in
    match uu____14955 with
    | hd1::uu____14961::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____14967 -> failwith "Impossible"
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
        | (uu____15016::uu____15017,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___157_15021 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___157_15021.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___157_15021.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___157_15021.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15022 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15033 =
        let uu____15035 =
          let uu____15036 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15036 in
        let uu____15037 = open_fact_db_tags env in uu____15035 :: uu____15037 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15033
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
      let uu____15052 = encode_sigelt env se in
      match uu____15052 with
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
        let uu____15077 = FStar_Options.log_queries () in
        if uu____15077
        then
          let uu____15079 =
            let uu____15080 =
              let uu____15081 =
                let uu____15082 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15082 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15081 in
            FStar_SMTEncoding_Term.Caption uu____15080 in
          uu____15079 :: decls
        else decls in
      let env =
        let uu____15089 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15089 tcenv in
      let uu____15090 = encode_top_level_facts env se in
      match uu____15090 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15099 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15099))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15110 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15110
       then
         let uu____15111 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15111
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15132  ->
                 fun se  ->
                   match uu____15132 with
                   | (g,env2) ->
                       let uu____15144 = encode_top_level_facts env2 se in
                       (match uu____15144 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15157 =
         encode_signature
           (let uu___158_15161 = env in
            {
              bindings = (uu___158_15161.bindings);
              depth = (uu___158_15161.depth);
              tcenv = (uu___158_15161.tcenv);
              warn = false;
              cache = (uu___158_15161.cache);
              nolabels = (uu___158_15161.nolabels);
              use_zfuel_name = (uu___158_15161.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___158_15161.encode_non_total_function_typ);
              current_module_name = (uu___158_15161.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15157 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15173 = FStar_Options.log_queries () in
             if uu____15173
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___159_15178 = env1 in
               {
                 bindings = (uu___159_15178.bindings);
                 depth = (uu___159_15178.depth);
                 tcenv = (uu___159_15178.tcenv);
                 warn = true;
                 cache = (uu___159_15178.cache);
                 nolabels = (uu___159_15178.nolabels);
                 use_zfuel_name = (uu___159_15178.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___159_15178.encode_non_total_function_typ);
                 current_module_name = (uu___159_15178.current_module_name)
               });
            (let uu____15180 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15180
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
        (let uu____15215 =
           let uu____15216 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15216.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15215);
        (let env =
           let uu____15218 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15218 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15225 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15246 = aux rest in
                 (match uu____15246 with
                  | (out,rest1) ->
                      let t =
                        let uu____15264 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15264 with
                        | Some uu____15268 ->
                            let uu____15269 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15269
                              x.FStar_Syntax_Syntax.sort
                        | uu____15270 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15273 =
                        let uu____15275 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___160_15276 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___160_15276.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___160_15276.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15275 :: out in
                      (uu____15273, rest1))
             | uu____15279 -> ([], bindings1) in
           let uu____15283 = aux bindings in
           match uu____15283 with
           | (closing,bindings1) ->
               let uu____15297 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15297, bindings1) in
         match uu____15225 with
         | (q1,bindings1) ->
             let uu____15310 =
               let uu____15313 =
                 FStar_List.filter
                   (fun uu___126_15315  ->
                      match uu___126_15315 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15316 ->
                          false
                      | uu____15320 -> true) bindings1 in
               encode_env_bindings env uu____15313 in
             (match uu____15310 with
              | (env_decls,env1) ->
                  ((let uu____15331 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15331
                    then
                      let uu____15332 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15332
                    else ());
                   (let uu____15334 = encode_formula q1 env1 in
                    match uu____15334 with
                    | (phi,qdecls) ->
                        let uu____15346 =
                          let uu____15349 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15349 phi in
                        (match uu____15346 with
                         | (labels,phi1) ->
                             let uu____15359 = encode_labels labels in
                             (match uu____15359 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15380 =
                                      let uu____15384 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15385 =
                                        varops.mk_unique "@query" in
                                      (uu____15384, (Some "query"),
                                        uu____15385) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15380 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15398 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15398 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15400 = encode_formula q env in
       match uu____15400 with
       | (f,uu____15404) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15406) -> true
             | uu____15409 -> false)))