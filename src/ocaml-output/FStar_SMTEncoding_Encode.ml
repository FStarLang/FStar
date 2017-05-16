open Prims
let add_fuel x tl1 =
  let uu____16 = FStar_Options.unthrottle_inductives () in
  if uu____16 then tl1 else x :: tl1
let withenv c uu____39 = match uu____39 with | (a,b) -> (a, b, c)
let vargs args =
  FStar_List.filter
    (fun uu___105_74  ->
       match uu___105_74 with
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
        let uu___130_140 = a in
        let uu____141 =
          FStar_Syntax_Util.unmangle_field_name a.FStar_Syntax_Syntax.ppname in
        {
          FStar_Syntax_Syntax.ppname = uu____141;
          FStar_Syntax_Syntax.index =
            (uu___130_140.FStar_Syntax_Syntax.index);
          FStar_Syntax_Syntax.sort = (uu___130_140.FStar_Syntax_Syntax.sort)
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
    let uu___131_780 = x in
    let uu____781 =
      FStar_Syntax_Util.unmangle_field_name x.FStar_Syntax_Syntax.ppname in
    {
      FStar_Syntax_Syntax.ppname = uu____781;
      FStar_Syntax_Syntax.index = (uu___131_780.FStar_Syntax_Syntax.index);
      FStar_Syntax_Syntax.sort = (uu___131_780.FStar_Syntax_Syntax.sort)
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
         (fun uu___106_1001  ->
            match uu___106_1001 with
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
           (fun uu___107_1016  ->
              match uu___107_1016 with
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
        (let uu___132_1080 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (env.depth + (Prims.parse_int "1"));
           tcenv = (uu___132_1080.tcenv);
           warn = (uu___132_1080.warn);
           cache = (uu___132_1080.cache);
           nolabels = (uu___132_1080.nolabels);
           use_zfuel_name = (uu___132_1080.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___132_1080.encode_non_total_function_typ);
           current_module_name = (uu___132_1080.current_module_name)
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
        (let uu___133_1093 = env in
         {
           bindings = ((Binding_var (x, y)) :: (env.bindings));
           depth = (uu___133_1093.depth);
           tcenv = (uu___133_1093.tcenv);
           warn = (uu___133_1093.warn);
           cache = (uu___133_1093.cache);
           nolabels = (uu___133_1093.nolabels);
           use_zfuel_name = (uu___133_1093.use_zfuel_name);
           encode_non_total_function_typ =
             (uu___133_1093.encode_non_total_function_typ);
           current_module_name = (uu___133_1093.current_module_name)
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
          (let uu___134_1109 = env in
           {
             bindings = ((Binding_var (x, y)) :: (env.bindings));
             depth = (uu___134_1109.depth);
             tcenv = (uu___134_1109.tcenv);
             warn = (uu___134_1109.warn);
             cache = (uu___134_1109.cache);
             nolabels = (uu___134_1109.nolabels);
             use_zfuel_name = (uu___134_1109.use_zfuel_name);
             encode_non_total_function_typ =
               (uu___134_1109.encode_non_total_function_typ);
             current_module_name = (uu___134_1109.current_module_name)
           }))
let push_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term -> env_t =
  fun env  ->
    fun x  ->
      fun t  ->
        let uu___135_1119 = env in
        {
          bindings = ((Binding_var (x, t)) :: (env.bindings));
          depth = (uu___135_1119.depth);
          tcenv = (uu___135_1119.tcenv);
          warn = (uu___135_1119.warn);
          cache = (uu___135_1119.cache);
          nolabels = (uu___135_1119.nolabels);
          use_zfuel_name = (uu___135_1119.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___135_1119.encode_non_total_function_typ);
          current_module_name = (uu___135_1119.current_module_name)
        }
let lookup_term_var:
  env_t -> FStar_Syntax_Syntax.bv -> FStar_SMTEncoding_Term.term =
  fun env  ->
    fun a  ->
      let aux a' =
        lookup_binding env
          (fun uu___108_1135  ->
             match uu___108_1135 with
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
        let uu___136_1182 = env in
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
          depth = (uu___136_1182.depth);
          tcenv = (uu___136_1182.tcenv);
          warn = (uu___136_1182.warn);
          cache = (uu___136_1182.cache);
          nolabels = (uu___136_1182.nolabels);
          use_zfuel_name = (uu___136_1182.use_zfuel_name);
          encode_non_total_function_typ =
            (uu___136_1182.encode_non_total_function_typ);
          current_module_name = (uu___136_1182.current_module_name)
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
        (fun uu___109_1217  ->
           match uu___109_1217 with
           | Binding_fvar (b,t1,t2,t3) when FStar_Ident.lid_equals b a ->
               Some (t1, t2, t3)
           | uu____1239 -> None)
let contains_name: env_t -> Prims.string -> Prims.bool =
  fun env  ->
    fun s  ->
      let uu____1251 =
        lookup_binding env
          (fun uu___110_1253  ->
             match uu___110_1253 with
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
          let uu___137_1325 = env in
          {
            bindings = ((Binding_fvar (x, fname, ftok, None)) ::
              (env.bindings));
            depth = (uu___137_1325.depth);
            tcenv = (uu___137_1325.tcenv);
            warn = (uu___137_1325.warn);
            cache = (uu___137_1325.cache);
            nolabels = (uu___137_1325.nolabels);
            use_zfuel_name = (uu___137_1325.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___137_1325.encode_non_total_function_typ);
            current_module_name = (uu___137_1325.current_module_name)
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
            let uu___138_1360 = env in
            {
              bindings = ((Binding_fvar (x, t1, t2, (Some t3))) ::
                (env.bindings));
              depth = (uu___138_1360.depth);
              tcenv = (uu___138_1360.tcenv);
              warn = (uu___138_1360.warn);
              cache = (uu___138_1360.cache);
              nolabels = (uu___138_1360.nolabels);
              use_zfuel_name = (uu___138_1360.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___138_1360.encode_non_total_function_typ);
              current_module_name = (uu___138_1360.current_module_name)
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
        (fun uu___111_1538  ->
           match uu___111_1538 with
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
               (fun uu___112_1723  ->
                  match uu___112_1723 with
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
  fun uu___113_1828  ->
    match uu___113_1828 with
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
  fun uu___114_1985  ->
    match uu___114_1985 with
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
        (let uu____2224 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2224
         then
           let uu____2225 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2225
         else ());
        (let uu____2227 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2263  ->
                   fun b  ->
                     match uu____2263 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2306 =
                           let x = unmangle (Prims.fst b) in
                           let uu____2315 = gen_term_var env1 x in
                           match uu____2315 with
                           | (xxsym,xx,env') ->
                               let uu____2329 =
                                 let uu____2332 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2332 env1 xx in
                               (match uu____2329 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2306 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2227 with
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
          let uu____2420 = encode_term t env in
          match uu____2420 with
          | (t1,decls) ->
              let uu____2427 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2427, decls)
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
          let uu____2435 = encode_term t env in
          match uu____2435 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2444 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2444, decls)
               | Some f ->
                   let uu____2446 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2446, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2453 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2453
       then
         let uu____2454 = FStar_Syntax_Print.tag_of_term t in
         let uu____2455 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2456 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2454 uu____2455
           uu____2456
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed _|FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2461 =
             let uu____2462 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2463 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2464 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2465 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2462
               uu____2463 uu____2464 uu____2465 in
           failwith uu____2461
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2469 =
             let uu____2470 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2470 in
           failwith uu____2469
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2475) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2505) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2514 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2514, [])
       | FStar_Syntax_Syntax.Tm_type uu____2520 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2523) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2529 = encode_const c in (uu____2529, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2544 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2544 with
            | (binders1,res) ->
                let uu____2551 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2551
                then
                  let uu____2554 = encode_binders None binders1 env in
                  (match uu____2554 with
                   | (vars,guards,env',decls,uu____2569) ->
                       let fsym =
                         let uu____2579 = varops.fresh "f" in
                         (uu____2579, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2582 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___139_2586 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___139_2586.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___139_2586.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___139_2586.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___139_2586.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___139_2586.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___139_2586.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___139_2586.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___139_2586.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___139_2586.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___139_2586.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___139_2586.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___139_2586.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___139_2586.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___139_2586.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___139_2586.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___139_2586.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___139_2586.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___139_2586.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___139_2586.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___139_2586.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___139_2586.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___139_2586.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___139_2586.FStar_TypeChecker_Env.qname_and_index);
                              FStar_TypeChecker_Env.proof_ns =
                                (uu___139_2586.FStar_TypeChecker_Env.proof_ns)
                            }) res in
                       (match uu____2582 with
                        | (pre_opt,res_t) ->
                            let uu____2593 =
                              encode_term_pred None res_t env' app in
                            (match uu____2593 with
                             | (res_pred,decls') ->
                                 let uu____2600 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2607 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2607, [])
                                   | Some pre ->
                                       let uu____2610 =
                                         encode_formula pre env' in
                                       (match uu____2610 with
                                        | (guard,decls0) ->
                                            let uu____2618 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____2618, decls0)) in
                                 (match uu____2600 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____2626 =
                                          let uu____2632 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____2632) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____2626 in
                                      let cvars =
                                        let uu____2642 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____2642
                                          (FStar_List.filter
                                             (fun uu____2648  ->
                                                match uu____2648 with
                                                | (x,uu____2652) ->
                                                    x <> (Prims.fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____2663 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____2663 with
                                       | Some cache_entry ->
                                           let uu____2668 =
                                             let uu____2669 =
                                               let uu____2673 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____2673) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2669 in
                                           (uu____2668,
                                             (use_cache_entry cache_entry))
                                       | None  ->
                                           let tsym =
                                             let uu____2684 =
                                               let uu____2685 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____2685 in
                                             varops.mk_unique uu____2684 in
                                           let cvar_sorts =
                                             FStar_List.map Prims.snd cvars in
                                           let caption =
                                             let uu____2692 =
                                               FStar_Options.log_queries () in
                                             if uu____2692
                                             then
                                               let uu____2694 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____2694
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____2700 =
                                               let uu____2704 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____2704) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____2700 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____2712 =
                                               let uu____2716 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____2716, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2712 in
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
                                             let uu____2729 =
                                               let uu____2733 =
                                                 let uu____2734 =
                                                   let uu____2740 =
                                                     let uu____2741 =
                                                       let uu____2744 =
                                                         let uu____2745 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____2745 in
                                                       (f_has_t, uu____2744) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____2741 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____2740) in
                                                 mkForall_fuel uu____2734 in
                                               (uu____2733,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2729 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____2758 =
                                               let uu____2762 =
                                                 let uu____2763 =
                                                   let uu____2769 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____2769) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____2763 in
                                               (uu____2762, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____2758 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____2783 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____2783);
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
                     let uu____2794 =
                       let uu____2798 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____2798, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2794 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____2807 =
                       let uu____2811 =
                         let uu____2812 =
                           let uu____2818 =
                             let uu____2819 =
                               let uu____2822 =
                                 let uu____2823 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____2823 in
                               (f_has_t, uu____2822) in
                             FStar_SMTEncoding_Util.mkImp uu____2819 in
                           ([[f_has_t]], [fsym], uu____2818) in
                         mkForall_fuel uu____2812 in
                       (uu____2811, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____2807 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____2837 ->
           let uu____2842 =
             let uu____2845 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____2845 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____2850;
                 FStar_Syntax_Syntax.pos = uu____2851;
                 FStar_Syntax_Syntax.vars = uu____2852;_} ->
                 let uu____2859 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____2859 with
                  | (b,f1) ->
                      let uu____2873 =
                        let uu____2874 = FStar_List.hd b in
                        Prims.fst uu____2874 in
                      (uu____2873, f1))
             | uu____2879 -> failwith "impossible" in
           (match uu____2842 with
            | (x,f) ->
                let uu____2886 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____2886 with
                 | (base_t,decls) ->
                     let uu____2893 = gen_term_var env x in
                     (match uu____2893 with
                      | (x1,xtm,env') ->
                          let uu____2902 = encode_formula f env' in
                          (match uu____2902 with
                           | (refinement,decls') ->
                               let uu____2909 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____2909 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____2920 =
                                        let uu____2922 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____2926 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____2922
                                          uu____2926 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____2920 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____2942  ->
                                              match uu____2942 with
                                              | (y,uu____2946) ->
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
                                    let uu____2965 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____2965 with
                                     | Some cache_entry ->
                                         let uu____2970 =
                                           let uu____2971 =
                                             let uu____2975 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____2975) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2971 in
                                         (uu____2970,
                                           (use_cache_entry cache_entry))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____2987 =
                                             let uu____2988 =
                                               let uu____2989 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____2989 in
                                             Prims.strcat module_name
                                               uu____2988 in
                                           varops.mk_unique uu____2987 in
                                         let cvar_sorts =
                                           FStar_List.map Prims.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____2998 =
                                             let uu____3002 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3002) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____2998 in
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
                                           let uu____3012 =
                                             let uu____3016 =
                                               let uu____3017 =
                                                 let uu____3023 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3023) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3017 in
                                             (uu____3016,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3012 in
                                         let t_kinding =
                                           let uu____3033 =
                                             let uu____3037 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3037,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3033 in
                                         let t_interp =
                                           let uu____3047 =
                                             let uu____3051 =
                                               let uu____3052 =
                                                 let uu____3058 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3058) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3052 in
                                             let uu____3070 =
                                               let uu____3072 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3072 in
                                             (uu____3051, uu____3070,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3047 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3077 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3077);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3094 = FStar_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3094 in
           let uu____3098 = encode_term_pred None k env ttm in
           (match uu____3098 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3106 =
                    let uu____3110 =
                      let uu____3111 =
                        let uu____3112 =
                          let uu____3113 = FStar_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3113 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3112 in
                      varops.mk_unique uu____3111 in
                    (t_has_k, (Some "Uvar typing"), uu____3110) in
                  FStar_SMTEncoding_Util.mkAssume uu____3106 in
                (ttm, (FStar_List.append decls [d])))
       | FStar_Syntax_Syntax.Tm_app uu____3119 ->
           let uu____3129 = FStar_Syntax_Util.head_and_args t0 in
           (match uu____3129 with
            | (head1,args_e) ->
                let uu____3157 =
                  let uu____3165 =
                    let uu____3166 = FStar_Syntax_Subst.compress head1 in
                    uu____3166.FStar_Syntax_Syntax.n in
                  (uu____3165, args_e) in
                (match uu____3157 with
                 | (uu____3176,uu____3177) when head_redex env head1 ->
                     let uu____3188 = whnf env t in
                     encode_term uu____3188 env
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
                     let uu____3262 = encode_term v1 env in
                     (match uu____3262 with
                      | (v11,decls1) ->
                          let uu____3269 = encode_term v2 env in
                          (match uu____3269 with
                           | (v21,decls2) ->
                               let uu____3276 =
                                 FStar_SMTEncoding_Util.mk_LexCons v11 v21 in
                               (uu____3276,
                                 (FStar_List.append decls1 decls2))))
                 | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_reify
                    ),uu____3278) ->
                     let e0 =
                       let uu____3290 = FStar_List.hd args_e in
                       FStar_TypeChecker_Util.reify_body_with_arg env.tcenv
                         head1 uu____3290 in
                     ((let uu____3296 =
                         FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug env.tcenv)
                           (FStar_Options.Other "SMTEncodingReify") in
                       if uu____3296
                       then
                         let uu____3297 =
                           FStar_Syntax_Print.term_to_string e0 in
                         FStar_Util.print1 "Result of normalization %s\n"
                           uu____3297
                       else ());
                      (let e =
                         let uu____3302 =
                           let uu____3303 =
                             FStar_TypeChecker_Util.remove_reify e0 in
                           let uu____3304 = FStar_List.tl args_e in
                           FStar_Syntax_Syntax.mk_Tm_app uu____3303
                             uu____3304 in
                         uu____3302 None t0.FStar_Syntax_Syntax.pos in
                       encode_term e env))
                 | (FStar_Syntax_Syntax.Tm_constant
                    (FStar_Const.Const_reflect
                    uu____3313),(arg,uu____3315)::[]) -> encode_term arg env
                 | uu____3333 ->
                     let uu____3341 = encode_args args_e env in
                     (match uu____3341 with
                      | (args,decls) ->
                          let encode_partial_app ht_opt =
                            let uu____3374 = encode_term head1 env in
                            match uu____3374 with
                            | (head2,decls') ->
                                let app_tm = mk_Apply_args head2 args in
                                (match ht_opt with
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
                                     let uu____3413 =
                                       FStar_Util.first_N
                                         (FStar_List.length args_e) formals in
                                     (match uu____3413 with
                                      | (formals1,rest) ->
                                          let subst1 =
                                            FStar_List.map2
                                              (fun uu____3455  ->
                                                 fun uu____3456  ->
                                                   match (uu____3455,
                                                           uu____3456)
                                                   with
                                                   | ((bv,uu____3470),
                                                      (a,uu____3472)) ->
                                                       FStar_Syntax_Syntax.NT
                                                         (bv, a)) formals1
                                              args_e in
                                          let ty =
                                            let uu____3486 =
                                              FStar_Syntax_Util.arrow rest c in
                                            FStar_All.pipe_right uu____3486
                                              (FStar_Syntax_Subst.subst
                                                 subst1) in
                                          let uu____3491 =
                                            encode_term_pred None ty env
                                              app_tm in
                                          (match uu____3491 with
                                           | (has_type,decls'') ->
                                               let cvars =
                                                 FStar_SMTEncoding_Term.free_variables
                                                   has_type in
                                               let e_typing =
                                                 let uu____3501 =
                                                   let uu____3505 =
                                                     FStar_SMTEncoding_Util.mkForall
                                                       ([[has_type]], cvars,
                                                         has_type) in
                                                   let uu____3510 =
                                                     let uu____3511 =
                                                       let uu____3512 =
                                                         let uu____3513 =
                                                           FStar_SMTEncoding_Term.hash_of_term
                                                             app_tm in
                                                         FStar_Util.digest_of_string
                                                           uu____3513 in
                                                       Prims.strcat
                                                         "partial_app_typing_"
                                                         uu____3512 in
                                                     varops.mk_unique
                                                       uu____3511 in
                                                   (uu____3505,
                                                     (Some
                                                        "Partial app typing"),
                                                     uu____3510) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____3501 in
                                               (app_tm,
                                                 (FStar_List.append decls
                                                    (FStar_List.append decls'
                                                       (FStar_List.append
                                                          decls'' [e_typing]))))))) in
                          let encode_full_app fv =
                            let uu____3530 = lookup_free_var_sym env fv in
                            match uu____3530 with
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
                                let uu____3568 =
                                  let uu____3569 =
                                    let uu____3572 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____3572 Prims.fst in
                                  FStar_All.pipe_right uu____3569 Prims.snd in
                                Some uu____3568
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3591,(FStar_Util.Inl t1,uu____3593),uu____3594)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____3632,(FStar_Util.Inr c,uu____3634),uu____3635)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____3673 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
                               let head_type2 =
                                 let uu____3693 =
                                   FStar_TypeChecker_Normalize.normalize_refinement
                                     [FStar_TypeChecker_Normalize.WHNF;
                                     FStar_TypeChecker_Normalize.EraseUniverses]
                                     env.tcenv head_type1 in
                                 FStar_All.pipe_left
                                   FStar_Syntax_Util.unrefine uu____3693 in
                               let uu____3694 =
                                 curried_arrow_formals_comp head_type2 in
                               (match uu____3694 with
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
                                     | uu____3719 ->
                                         if
                                           (FStar_List.length formals) >
                                             (FStar_List.length args)
                                         then
                                           encode_partial_app
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____3764 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____3764 with
            | (bs1,body1,opening) ->
                let fallback uu____3779 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
                  let uu____3784 =
                    FStar_SMTEncoding_Util.mkFreeV
                      (f, FStar_SMTEncoding_Term.Term_sort) in
                  (uu____3784, [decl]) in
                let is_impure lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3795 =
                        FStar_Syntax_Util.is_pure_or_ghost_lcomp lc1 in
                      Prims.op_Negation uu____3795
                  | FStar_Util.Inr (eff,uu____3797) ->
                      let uu____3803 =
                        FStar_TypeChecker_Util.is_pure_or_ghost_effect
                          env.tcenv eff in
                      FStar_All.pipe_right uu____3803 Prims.op_Negation in
                let reify_comp_and_body env1 c body2 =
                  let reified_body =
                    FStar_TypeChecker_Util.reify_body env1.tcenv body2 in
                  let c1 =
                    match c with
                    | FStar_Util.Inl lc ->
                        let typ =
                          let uu____3848 = lc.FStar_Syntax_Syntax.comp () in
                          FStar_TypeChecker_Env.reify_comp
                            (let uu___140_3849 = env1.tcenv in
                             {
                               FStar_TypeChecker_Env.solver =
                                 (uu___140_3849.FStar_TypeChecker_Env.solver);
                               FStar_TypeChecker_Env.range =
                                 (uu___140_3849.FStar_TypeChecker_Env.range);
                               FStar_TypeChecker_Env.curmodule =
                                 (uu___140_3849.FStar_TypeChecker_Env.curmodule);
                               FStar_TypeChecker_Env.gamma =
                                 (uu___140_3849.FStar_TypeChecker_Env.gamma);
                               FStar_TypeChecker_Env.gamma_cache =
                                 (uu___140_3849.FStar_TypeChecker_Env.gamma_cache);
                               FStar_TypeChecker_Env.modules =
                                 (uu___140_3849.FStar_TypeChecker_Env.modules);
                               FStar_TypeChecker_Env.expected_typ =
                                 (uu___140_3849.FStar_TypeChecker_Env.expected_typ);
                               FStar_TypeChecker_Env.sigtab =
                                 (uu___140_3849.FStar_TypeChecker_Env.sigtab);
                               FStar_TypeChecker_Env.is_pattern =
                                 (uu___140_3849.FStar_TypeChecker_Env.is_pattern);
                               FStar_TypeChecker_Env.instantiate_imp =
                                 (uu___140_3849.FStar_TypeChecker_Env.instantiate_imp);
                               FStar_TypeChecker_Env.effects =
                                 (uu___140_3849.FStar_TypeChecker_Env.effects);
                               FStar_TypeChecker_Env.generalize =
                                 (uu___140_3849.FStar_TypeChecker_Env.generalize);
                               FStar_TypeChecker_Env.letrecs =
                                 (uu___140_3849.FStar_TypeChecker_Env.letrecs);
                               FStar_TypeChecker_Env.top_level =
                                 (uu___140_3849.FStar_TypeChecker_Env.top_level);
                               FStar_TypeChecker_Env.check_uvars =
                                 (uu___140_3849.FStar_TypeChecker_Env.check_uvars);
                               FStar_TypeChecker_Env.use_eq =
                                 (uu___140_3849.FStar_TypeChecker_Env.use_eq);
                               FStar_TypeChecker_Env.is_iface =
                                 (uu___140_3849.FStar_TypeChecker_Env.is_iface);
                               FStar_TypeChecker_Env.admit =
                                 (uu___140_3849.FStar_TypeChecker_Env.admit);
                               FStar_TypeChecker_Env.lax = true;
                               FStar_TypeChecker_Env.lax_universes =
                                 (uu___140_3849.FStar_TypeChecker_Env.lax_universes);
                               FStar_TypeChecker_Env.type_of =
                                 (uu___140_3849.FStar_TypeChecker_Env.type_of);
                               FStar_TypeChecker_Env.universe_of =
                                 (uu___140_3849.FStar_TypeChecker_Env.universe_of);
                               FStar_TypeChecker_Env.use_bv_sorts =
                                 (uu___140_3849.FStar_TypeChecker_Env.use_bv_sorts);
                               FStar_TypeChecker_Env.qname_and_index =
                                 (uu___140_3849.FStar_TypeChecker_Env.qname_and_index);
                               FStar_TypeChecker_Env.proof_ns =
                                 (uu___140_3849.FStar_TypeChecker_Env.proof_ns)
                             }) uu____3848 FStar_Syntax_Syntax.U_unknown in
                        let uu____3850 =
                          let uu____3851 = FStar_Syntax_Syntax.mk_Total typ in
                          FStar_Syntax_Util.lcomp_of_comp uu____3851 in
                        FStar_Util.Inl uu____3850
                    | FStar_Util.Inr (eff_name,uu____3858) -> c in
                  (c1, reified_body) in
                let codomain_eff lc =
                  match lc with
                  | FStar_Util.Inl lc1 ->
                      let uu____3889 =
                        let uu____3890 = lc1.FStar_Syntax_Syntax.comp () in
                        FStar_Syntax_Subst.subst_comp opening uu____3890 in
                      FStar_All.pipe_right uu____3889
                        (fun _0_30  -> Some _0_30)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____3902 =
                        let uu____3903 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____3903 Prims.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____3911 =
                          let uu____3912 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____3912 in
                        FStar_All.pipe_right uu____3911
                          (fun _0_31  -> Some _0_31)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____3916 =
                             let uu____3917 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____3917 in
                           FStar_All.pipe_right uu____3916
                             (fun _0_32  -> Some _0_32))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____3928 =
                         let uu____3929 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____3929 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____3928);
                      fallback ())
                 | Some lc ->
                     let lc1 = lc in
                     let uu____3944 =
                       (is_impure lc1) &&
                         (let uu____3945 =
                            FStar_TypeChecker_Env.is_reifiable env.tcenv lc1 in
                          Prims.op_Negation uu____3945) in
                     if uu____3944
                     then fallback ()
                     else
                       (let cache_size = FStar_Util.smap_size env.cache in
                        let uu____3950 = encode_binders None bs1 env in
                        match uu____3950 with
                        | (vars,guards,envbody,decls,uu____3965) ->
                            let uu____3972 =
                              let uu____3980 =
                                FStar_TypeChecker_Env.is_reifiable env.tcenv
                                  lc1 in
                              if uu____3980
                              then reify_comp_and_body envbody lc1 body1
                              else (lc1, body1) in
                            (match uu____3972 with
                             | (lc2,body2) ->
                                 let uu____4005 = encode_term body2 envbody in
                                 (match uu____4005 with
                                  | (body3,decls') ->
                                      let uu____4012 =
                                        let uu____4017 = codomain_eff lc2 in
                                        match uu____4017 with
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4029 =
                                              encode_term tfun env in
                                            (match uu____4029 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
                                      (match uu____4012 with
                                       | (arrow_t_opt,decls'') ->
                                           let key_body =
                                             let uu____4048 =
                                               let uu____4054 =
                                                 let uu____4055 =
                                                   let uu____4058 =
                                                     FStar_SMTEncoding_Util.mk_and_l
                                                       guards in
                                                   (uu____4058, body3) in
                                                 FStar_SMTEncoding_Util.mkImp
                                                   uu____4055 in
                                               ([], vars, uu____4054) in
                                             FStar_SMTEncoding_Util.mkForall
                                               uu____4048 in
                                           let cvars =
                                             FStar_SMTEncoding_Term.free_variables
                                               key_body in
                                           let cvars1 =
                                             match arrow_t_opt with
                                             | None  -> cvars
                                             | Some t1 ->
                                                 let uu____4066 =
                                                   let uu____4068 =
                                                     FStar_SMTEncoding_Term.free_variables
                                                       t1 in
                                                   FStar_List.append
                                                     uu____4068 cvars in
                                                 FStar_Util.remove_dups
                                                   FStar_SMTEncoding_Term.fv_eq
                                                   uu____4066 in
                                           let tkey =
                                             FStar_SMTEncoding_Util.mkForall
                                               ([], cvars1, key_body) in
                                           let tkey_hash =
                                             FStar_SMTEncoding_Term.hash_of_term
                                               tkey in
                                           let uu____4079 =
                                             FStar_Util.smap_try_find
                                               env.cache tkey_hash in
                                           (match uu____4079 with
                                            | Some cache_entry ->
                                                let uu____4084 =
                                                  let uu____4085 =
                                                    let uu____4089 =
                                                      FStar_List.map
                                                        FStar_SMTEncoding_Util.mkFreeV
                                                        cvars1 in
                                                    ((cache_entry.cache_symbol_name),
                                                      uu____4089) in
                                                  FStar_SMTEncoding_Util.mkApp
                                                    uu____4085 in
                                                (uu____4084,
                                                  (use_cache_entry
                                                     cache_entry))
                                            | None  ->
                                                let uu____4095 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4095 with
                                                 | Some t1 ->
                                                     let decls1 =
                                                       let uu____4102 =
                                                         let uu____4103 =
                                                           FStar_Util.smap_size
                                                             env.cache in
                                                         uu____4103 =
                                                           cache_size in
                                                       if uu____4102
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
                                                         let uu____4114 =
                                                           let uu____4115 =
                                                             FStar_Util.digest_of_string
                                                               tkey_hash in
                                                           Prims.strcat
                                                             "Tm_abs_"
                                                             uu____4115 in
                                                         varops.mk_unique
                                                           uu____4114 in
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
                                                       let uu____4120 =
                                                         let uu____4124 =
                                                           FStar_List.map
                                                             FStar_SMTEncoding_Util.mkFreeV
                                                             cvars1 in
                                                         (fsym, uu____4124) in
                                                       FStar_SMTEncoding_Util.mkApp
                                                         uu____4120 in
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
                                                           let uu____4136 =
                                                             let uu____4137 =
                                                               let uu____4141
                                                                 =
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   ([[f]],
                                                                    cvars1,
                                                                    f_has_t) in
                                                               (uu____4141,
                                                                 (Some a_name),
                                                                 a_name) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____4137 in
                                                           [uu____4136] in
                                                     let interp_f =
                                                       let a_name =
                                                         Prims.strcat
                                                           "interpretation_"
                                                           fsym in
                                                       let uu____4149 =
                                                         let uu____4153 =
                                                           let uu____4154 =
                                                             let uu____4160 =
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 (app, body3) in
                                                             ([[app]],
                                                               (FStar_List.append
                                                                  vars cvars1),
                                                               uu____4160) in
                                                           FStar_SMTEncoding_Util.mkForall
                                                             uu____4154 in
                                                         (uu____4153,
                                                           (Some a_name),
                                                           a_name) in
                                                       FStar_SMTEncoding_Util.mkAssume
                                                         uu____4149 in
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
                                                     ((let uu____4170 =
                                                         mk_cache_entry env
                                                           fsym cvar_sorts
                                                           f_decls in
                                                       FStar_Util.smap_add
                                                         env.cache tkey_hash
                                                         uu____4170);
                                                      (f, f_decls))))))))))
       | FStar_Syntax_Syntax.Tm_let
           ((uu____4172,{
                          FStar_Syntax_Syntax.lbname = FStar_Util.Inr
                            uu____4173;
                          FStar_Syntax_Syntax.lbunivs = uu____4174;
                          FStar_Syntax_Syntax.lbtyp = uu____4175;
                          FStar_Syntax_Syntax.lbeff = uu____4176;
                          FStar_Syntax_Syntax.lbdef = uu____4177;_}::uu____4178),uu____4179)
           -> failwith "Impossible: already handled by encoding of Sig_let"
       | FStar_Syntax_Syntax.Tm_let
           ((false
             ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                FStar_Syntax_Syntax.lbunivs = uu____4197;
                FStar_Syntax_Syntax.lbtyp = t1;
                FStar_Syntax_Syntax.lbeff = uu____4199;
                FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
           -> encode_let x t1 e1 e2 env encode_term
       | FStar_Syntax_Syntax.Tm_let uu____4215 ->
           (FStar_Errors.diag t0.FStar_Syntax_Syntax.pos
              "Non-top-level recursive functions are not yet fully encoded to the SMT solver; you may not be able to prove some facts";
            (let e = varops.fresh "let-rec" in
             let decl_e =
               FStar_SMTEncoding_Term.DeclFun
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
             let uu____4228 =
               FStar_SMTEncoding_Util.mkFreeV
                 (e, FStar_SMTEncoding_Term.Term_sort) in
             (uu____4228, [decl_e])))
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
              let uu____4270 = encode_term e1 env in
              match uu____4270 with
              | (ee1,decls1) ->
                  let uu____4277 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
                  (match uu____4277 with
                   | (xs,e21) ->
                       let uu____4291 = FStar_List.hd xs in
                       (match uu____4291 with
                        | (x1,uu____4299) ->
                            let env' = push_term_var env x1 ee1 in
                            let uu____4301 = encode_body e21 env' in
                            (match uu____4301 with
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
            let uu____4323 =
              let uu____4327 =
                let uu____4328 =
                  (FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown)
                    None FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4328 in
              gen_term_var env uu____4327 in
            match uu____4323 with
            | (scrsym,scr',env1) ->
                let uu____4342 = encode_term e env1 in
                (match uu____4342 with
                 | (scr,decls) ->
                     let uu____4349 =
                       let encode_branch b uu____4365 =
                         match uu____4365 with
                         | (else_case,decls1) ->
                             let uu____4376 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4376 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4406  ->
                                       fun uu____4407  ->
                                         match (uu____4406, uu____4407) with
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
                                                       fun uu____4444  ->
                                                         match uu____4444
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4449 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4464 =
                                                     encode_term w1 env2 in
                                                   (match uu____4464 with
                                                    | (w2,decls21) ->
                                                        let uu____4472 =
                                                          let uu____4473 =
                                                            let uu____4476 =
                                                              let uu____4477
                                                                =
                                                                let uu____4480
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4480) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4477 in
                                                            (guard,
                                                              uu____4476) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4473 in
                                                        (uu____4472, decls21)) in
                                             (match uu____4449 with
                                              | (guard1,decls21) ->
                                                  let uu____4488 =
                                                    encode_br br env2 in
                                                  (match uu____4488 with
                                                   | (br1,decls3) ->
                                                       let uu____4496 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4496,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4349 with
                      | (match_tm,decls1) ->
                          let uu____4508 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4508, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4539 -> let uu____4540 = encode_one_pat env pat in [uu____4540]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4552 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4552
       then
         let uu____4553 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4553
       else ());
      (let uu____4555 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4555 with
       | (vars,pat_term) ->
           let uu____4565 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4588  ->
                     fun v1  ->
                       match uu____4588 with
                       | (env1,vars1) ->
                           let uu____4616 = gen_term_var env1 v1 in
                           (match uu____4616 with
                            | (xx,uu____4628,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4565 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4675 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4683 =
                        let uu____4686 = encode_const c in
                        (scrutinee, uu____4686) in
                      FStar_SMTEncoding_Util.mkEq uu____4683
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____4705 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____4705 with
                        | (uu____4709,uu____4710::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____4712 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4733  ->
                                  match uu____4733 with
                                  | (arg,uu____4739) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4749 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____4749)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4768 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____4783 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____4798 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____4820  ->
                                  match uu____4820 with
                                  | (arg,uu____4829) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____4839 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____4839)) in
                      FStar_All.pipe_right uu____4798 FStar_List.flatten in
                let pat_term1 uu____4855 = encode_term pat_term env1 in
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
      let uu____4862 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____4877  ->
                fun uu____4878  ->
                  match (uu____4877, uu____4878) with
                  | ((tms,decls),(t,uu____4898)) ->
                      let uu____4909 = encode_term t env in
                      (match uu____4909 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____4862 with | (l1,decls) -> ((FStar_List.rev l1), decls)
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
            let uu____4947 = FStar_Syntax_Util.list_elements e in
            match uu____4947 with
            | Some l -> l
            | None  ->
                (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
                   "SMT pattern is not a list literal; ignoring the pattern";
                 []) in
          let one_pat p =
            let uu____4965 =
              let uu____4975 = FStar_Syntax_Util.unmeta p in
              FStar_All.pipe_right uu____4975 FStar_Syntax_Util.head_and_args in
            match uu____4965 with
            | (head1,args) ->
                let uu____5006 =
                  let uu____5014 =
                    let uu____5015 = FStar_Syntax_Util.un_uinst head1 in
                    uu____5015.FStar_Syntax_Syntax.n in
                  (uu____5014, args) in
                (match uu____5006 with
                 | (FStar_Syntax_Syntax.Tm_fvar
                    fv,(uu____5029,uu____5030)::(e,uu____5032)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpat_lid
                     -> (e, None)
                 | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5063)::[]) when
                     FStar_Syntax_Syntax.fv_eq_lid fv
                       FStar_Syntax_Const.smtpatT_lid
                     -> (e, None)
                 | uu____5084 -> failwith "Unexpected pattern term") in
          let lemma_pats p =
            let elts = list_elements1 p in
            let smt_pat_or t1 =
              let uu____5117 =
                let uu____5127 = FStar_Syntax_Util.unmeta t1 in
                FStar_All.pipe_right uu____5127
                  FStar_Syntax_Util.head_and_args in
              match uu____5117 with
              | (head1,args) ->
                  let uu____5156 =
                    let uu____5164 =
                      let uu____5165 = FStar_Syntax_Util.un_uinst head1 in
                      uu____5165.FStar_Syntax_Syntax.n in
                    (uu____5164, args) in
                  (match uu____5156 with
                   | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5178)::[]) when
                       FStar_Syntax_Syntax.fv_eq_lid fv
                         FStar_Syntax_Const.smtpatOr_lid
                       -> Some e
                   | uu____5198 -> None) in
            match elts with
            | t1::[] ->
                let uu____5216 = smt_pat_or t1 in
                (match uu____5216 with
                 | Some e ->
                     let uu____5232 = list_elements1 e in
                     FStar_All.pipe_right uu____5232
                       (FStar_List.map
                          (fun branch1  ->
                             let uu____5249 = list_elements1 branch1 in
                             FStar_All.pipe_right uu____5249
                               (FStar_List.map one_pat)))
                 | uu____5263 ->
                     let uu____5267 =
                       FStar_All.pipe_right elts (FStar_List.map one_pat) in
                     [uu____5267])
            | uu____5298 ->
                let uu____5300 =
                  FStar_All.pipe_right elts (FStar_List.map one_pat) in
                [uu____5300] in
          let uu____5331 =
            let uu____5347 =
              let uu____5348 = FStar_Syntax_Subst.compress t in
              uu____5348.FStar_Syntax_Syntax.n in
            match uu____5347 with
            | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
                let uu____5378 = FStar_Syntax_Subst.open_comp binders c in
                (match uu____5378 with
                 | (binders1,c1) ->
                     (match c1.FStar_Syntax_Syntax.n with
                      | FStar_Syntax_Syntax.Comp
                          { FStar_Syntax_Syntax.comp_univs = uu____5413;
                            FStar_Syntax_Syntax.effect_name = uu____5414;
                            FStar_Syntax_Syntax.result_typ = uu____5415;
                            FStar_Syntax_Syntax.effect_args =
                              (pre,uu____5417)::(post,uu____5419)::(pats,uu____5421)::[];
                            FStar_Syntax_Syntax.flags = uu____5422;_}
                          ->
                          let pats' =
                            match new_pats with
                            | Some new_pats' -> new_pats'
                            | None  -> pats in
                          let uu____5456 = lemma_pats pats' in
                          (binders1, pre, post, uu____5456)
                      | uu____5475 -> failwith "impos"))
            | uu____5491 -> failwith "Impos" in
          match uu____5331 with
          | (binders,pre,post,patterns) ->
              let uu____5535 = encode_binders None binders env in
              (match uu____5535 with
               | (vars,guards,env1,decls,uu____5550) ->
                   let uu____5557 =
                     let uu____5564 =
                       FStar_All.pipe_right patterns
                         (FStar_List.map
                            (fun branch1  ->
                               let uu____5595 =
                                 let uu____5600 =
                                   FStar_All.pipe_right branch1
                                     (FStar_List.map
                                        (fun uu____5616  ->
                                           match uu____5616 with
                                           | (t1,uu____5623) ->
                                               encode_term t1
                                                 (let uu___141_5626 = env1 in
                                                  {
                                                    bindings =
                                                      (uu___141_5626.bindings);
                                                    depth =
                                                      (uu___141_5626.depth);
                                                    tcenv =
                                                      (uu___141_5626.tcenv);
                                                    warn =
                                                      (uu___141_5626.warn);
                                                    cache =
                                                      (uu___141_5626.cache);
                                                    nolabels =
                                                      (uu___141_5626.nolabels);
                                                    use_zfuel_name = true;
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___141_5626.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___141_5626.current_module_name)
                                                  }))) in
                                 FStar_All.pipe_right uu____5600
                                   FStar_List.unzip in
                               match uu____5595 with
                               | (pats,decls1) -> (pats, decls1))) in
                     FStar_All.pipe_right uu____5564 FStar_List.unzip in
                   (match uu____5557 with
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
                                           let uu____5690 =
                                             let uu____5691 =
                                               FStar_SMTEncoding_Util.mkFreeV
                                                 l in
                                             FStar_SMTEncoding_Util.mk_Precedes
                                               uu____5691 e in
                                           uu____5690 :: p))
                               | uu____5692 ->
                                   let rec aux tl1 vars1 =
                                     match vars1 with
                                     | [] ->
                                         FStar_All.pipe_right pats
                                           (FStar_List.map
                                              (fun p  ->
                                                 let uu____5721 =
                                                   FStar_SMTEncoding_Util.mk_Precedes
                                                     tl1 e in
                                                 uu____5721 :: p))
                                     | (x,FStar_SMTEncoding_Term.Term_sort )::vars2
                                         ->
                                         let uu____5729 =
                                           let uu____5730 =
                                             FStar_SMTEncoding_Util.mkFreeV
                                               (x,
                                                 FStar_SMTEncoding_Term.Term_sort) in
                                           FStar_SMTEncoding_Util.mk_LexCons
                                             uu____5730 tl1 in
                                         aux uu____5729 vars2
                                     | uu____5731 -> pats in
                                   let uu____5735 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       ("Prims.LexTop",
                                         FStar_SMTEncoding_Term.Term_sort) in
                                   aux uu____5735 vars) in
                        let env2 =
                          let uu___142_5737 = env1 in
                          {
                            bindings = (uu___142_5737.bindings);
                            depth = (uu___142_5737.depth);
                            tcenv = (uu___142_5737.tcenv);
                            warn = (uu___142_5737.warn);
                            cache = (uu___142_5737.cache);
                            nolabels = true;
                            use_zfuel_name = (uu___142_5737.use_zfuel_name);
                            encode_non_total_function_typ =
                              (uu___142_5737.encode_non_total_function_typ);
                            current_module_name =
                              (uu___142_5737.current_module_name)
                          } in
                        let uu____5738 =
                          let uu____5741 = FStar_Syntax_Util.unmeta pre in
                          encode_formula uu____5741 env2 in
                        (match uu____5738 with
                         | (pre1,decls'') ->
                             let uu____5746 =
                               let uu____5749 = FStar_Syntax_Util.unmeta post in
                               encode_formula uu____5749 env2 in
                             (match uu____5746 with
                              | (post1,decls''') ->
                                  let decls1 =
                                    FStar_List.append decls
                                      (FStar_List.append
                                         (FStar_List.flatten decls'1)
                                         (FStar_List.append decls'' decls''')) in
                                  let uu____5756 =
                                    let uu____5757 =
                                      let uu____5763 =
                                        let uu____5764 =
                                          let uu____5767 =
                                            FStar_SMTEncoding_Util.mk_and_l
                                              (pre1 :: guards) in
                                          (uu____5767, post1) in
                                        FStar_SMTEncoding_Util.mkImp
                                          uu____5764 in
                                      (pats1, vars, uu____5763) in
                                    FStar_SMTEncoding_Util.mkForall
                                      uu____5757 in
                                  (uu____5756, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____5780 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____5780
        then
          let uu____5781 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____5782 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____5781 uu____5782
        else () in
      let enc f r l =
        let uu____5809 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____5822 = encode_term (Prims.fst x) env in
                 match uu____5822 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____5809 with
        | (decls,args) ->
            let uu____5839 =
              let uu___143_5840 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___143_5840.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___143_5840.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5839, decls) in
      let const_op f r uu____5859 = let uu____5862 = f r in (uu____5862, []) in
      let un_op f l =
        let uu____5878 = FStar_List.hd l in FStar_All.pipe_left f uu____5878 in
      let bin_op f uu___115_5891 =
        match uu___115_5891 with
        | t1::t2::[] -> f (t1, t2)
        | uu____5899 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____5926 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____5935  ->
                 match uu____5935 with
                 | (t,uu____5943) ->
                     let uu____5944 = encode_formula t env in
                     (match uu____5944 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____5926 with
        | (decls,phis) ->
            let uu____5961 =
              let uu___144_5962 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___144_5962.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___144_5962.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____5961, decls) in
      let eq_op r uu___116_5978 =
        match uu___116_5978 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6038 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6038 r [e1; e2]
        | l ->
            let uu____6058 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6058 r l in
      let mk_imp1 r uu___117_6077 =
        match uu___117_6077 with
        | (lhs,uu____6081)::(rhs,uu____6083)::[] ->
            let uu____6104 = encode_formula rhs env in
            (match uu____6104 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6113) ->
                      (l1, decls1)
                  | uu____6116 ->
                      let uu____6117 = encode_formula lhs env in
                      (match uu____6117 with
                       | (l2,decls2) ->
                           let uu____6124 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6124, (FStar_List.append decls1 decls2)))))
        | uu____6126 -> failwith "impossible" in
      let mk_ite r uu___118_6141 =
        match uu___118_6141 with
        | (guard,uu____6145)::(_then,uu____6147)::(_else,uu____6149)::[] ->
            let uu____6178 = encode_formula guard env in
            (match uu____6178 with
             | (g,decls1) ->
                 let uu____6185 = encode_formula _then env in
                 (match uu____6185 with
                  | (t,decls2) ->
                      let uu____6192 = encode_formula _else env in
                      (match uu____6192 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6201 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6220 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6220 in
      let connectives =
        let uu____6232 =
          let uu____6241 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6241) in
        let uu____6254 =
          let uu____6264 =
            let uu____6273 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6273) in
          let uu____6286 =
            let uu____6296 =
              let uu____6306 =
                let uu____6315 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6315) in
              let uu____6328 =
                let uu____6338 =
                  let uu____6348 =
                    let uu____6357 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6357) in
                  [uu____6348;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6338 in
              uu____6306 :: uu____6328 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6296 in
          uu____6264 :: uu____6286 in
        uu____6232 :: uu____6254 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6519 = encode_formula phi' env in
            (match uu____6519 with
             | (phi2,decls) ->
                 let uu____6526 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6526, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6527 ->
            let uu____6532 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6532 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6561 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6561 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6569;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6571;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6587 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6587 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6619::(x,uu____6621)::(t,uu____6623)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6657 = encode_term x env in
                 (match uu____6657 with
                  | (x1,decls) ->
                      let uu____6664 = encode_term t env in
                      (match uu____6664 with
                       | (t1,decls') ->
                           let uu____6671 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6671, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6675)::(msg,uu____6677)::(phi2,uu____6679)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6713 =
                   let uu____6716 =
                     let uu____6717 = FStar_Syntax_Subst.compress r in
                     uu____6717.FStar_Syntax_Syntax.n in
                   let uu____6720 =
                     let uu____6721 = FStar_Syntax_Subst.compress msg in
                     uu____6721.FStar_Syntax_Syntax.n in
                   (uu____6716, uu____6720) in
                 (match uu____6713 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6728))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6744 -> fallback phi2)
             | uu____6747 when head_redex env head2 ->
                 let uu____6755 = whnf env phi1 in
                 encode_formula uu____6755 env
             | uu____6756 ->
                 let uu____6764 = encode_term phi1 env in
                 (match uu____6764 with
                  | (tt,decls) ->
                      let uu____6771 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___145_6772 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___145_6772.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___145_6772.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____6771, decls)))
        | uu____6775 ->
            let uu____6776 = encode_term phi1 env in
            (match uu____6776 with
             | (tt,decls) ->
                 let uu____6783 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___146_6784 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___146_6784.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___146_6784.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____6783, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____6811 = encode_binders None bs env1 in
        match uu____6811 with
        | (vars,guards,env2,decls,uu____6833) ->
            let uu____6840 =
              let uu____6847 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____6870 =
                          let uu____6875 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____6889  ->
                                    match uu____6889 with
                                    | (t,uu____6895) ->
                                        encode_term t
                                          (let uu___147_6896 = env2 in
                                           {
                                             bindings =
                                               (uu___147_6896.bindings);
                                             depth = (uu___147_6896.depth);
                                             tcenv = (uu___147_6896.tcenv);
                                             warn = (uu___147_6896.warn);
                                             cache = (uu___147_6896.cache);
                                             nolabels =
                                               (uu___147_6896.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___147_6896.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___147_6896.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____6875 FStar_List.unzip in
                        match uu____6870 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____6847 FStar_List.unzip in
            (match uu____6840 with
             | (pats,decls') ->
                 let uu____6948 = encode_formula body env2 in
                 (match uu____6948 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____6967;
                             FStar_SMTEncoding_Term.rng = uu____6968;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____6976 -> guards in
                      let uu____6979 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____6979, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7013  ->
                   match uu____7013 with
                   | (x,uu____7017) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7023 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7029 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7029) uu____7023 tl1 in
             let uu____7031 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7043  ->
                       match uu____7043 with
                       | (b,uu____7047) ->
                           let uu____7048 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7048)) in
             (match uu____7031 with
              | None  -> ()
              | Some (x,uu____7052) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7062 =
                    let uu____7063 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7063 in
                  FStar_Errors.warn pos uu____7062) in
       let uu____7064 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7064 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7070 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7106  ->
                     match uu____7106 with
                     | (l,uu____7116) -> FStar_Ident.lid_equals op l)) in
           (match uu____7070 with
            | None  -> fallback phi1
            | Some (uu____7139,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7168 = encode_q_body env vars pats body in
             match uu____7168 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7194 =
                     let uu____7200 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7200) in
                   FStar_SMTEncoding_Term.mkForall uu____7194
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7212 = encode_q_body env vars pats body in
             match uu____7212 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7237 =
                   let uu____7238 =
                     let uu____7244 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7244) in
                   FStar_SMTEncoding_Term.mkExists uu____7238
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7237, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7293 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7293 with
  | (asym,a) ->
      let uu____7298 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7298 with
       | (xsym,x) ->
           let uu____7303 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7303 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7333 =
                      let uu____7339 =
                        FStar_All.pipe_right vars (FStar_List.map Prims.snd) in
                      (x1, uu____7339, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7333 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7354 =
                      let uu____7358 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7358) in
                    FStar_SMTEncoding_Util.mkApp uu____7354 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7366 =
                    let uu____7368 =
                      let uu____7370 =
                        let uu____7372 =
                          let uu____7373 =
                            let uu____7377 =
                              let uu____7378 =
                                let uu____7384 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7384) in
                              FStar_SMTEncoding_Util.mkForall uu____7378 in
                            (uu____7377, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7373 in
                        let uu____7393 =
                          let uu____7395 =
                            let uu____7396 =
                              let uu____7400 =
                                let uu____7401 =
                                  let uu____7407 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7407) in
                                FStar_SMTEncoding_Util.mkForall uu____7401 in
                              (uu____7400,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7396 in
                          [uu____7395] in
                        uu____7372 :: uu____7393 in
                      xtok_decl :: uu____7370 in
                    xname_decl :: uu____7368 in
                  (xtok1, uu____7366) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7456 =
                    let uu____7464 =
                      let uu____7470 =
                        let uu____7471 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7471 in
                      quant axy uu____7470 in
                    (FStar_Syntax_Const.op_Eq, uu____7464) in
                  let uu____7477 =
                    let uu____7486 =
                      let uu____7494 =
                        let uu____7500 =
                          let uu____7501 =
                            let uu____7502 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7502 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7501 in
                        quant axy uu____7500 in
                      (FStar_Syntax_Const.op_notEq, uu____7494) in
                    let uu____7508 =
                      let uu____7517 =
                        let uu____7525 =
                          let uu____7531 =
                            let uu____7532 =
                              let uu____7533 =
                                let uu____7536 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7537 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7536, uu____7537) in
                              FStar_SMTEncoding_Util.mkLT uu____7533 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7532 in
                          quant xy uu____7531 in
                        (FStar_Syntax_Const.op_LT, uu____7525) in
                      let uu____7543 =
                        let uu____7552 =
                          let uu____7560 =
                            let uu____7566 =
                              let uu____7567 =
                                let uu____7568 =
                                  let uu____7571 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7572 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7571, uu____7572) in
                                FStar_SMTEncoding_Util.mkLTE uu____7568 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7567 in
                            quant xy uu____7566 in
                          (FStar_Syntax_Const.op_LTE, uu____7560) in
                        let uu____7578 =
                          let uu____7587 =
                            let uu____7595 =
                              let uu____7601 =
                                let uu____7602 =
                                  let uu____7603 =
                                    let uu____7606 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7607 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7606, uu____7607) in
                                  FStar_SMTEncoding_Util.mkGT uu____7603 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7602 in
                              quant xy uu____7601 in
                            (FStar_Syntax_Const.op_GT, uu____7595) in
                          let uu____7613 =
                            let uu____7622 =
                              let uu____7630 =
                                let uu____7636 =
                                  let uu____7637 =
                                    let uu____7638 =
                                      let uu____7641 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7642 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7641, uu____7642) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7638 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7637 in
                                quant xy uu____7636 in
                              (FStar_Syntax_Const.op_GTE, uu____7630) in
                            let uu____7648 =
                              let uu____7657 =
                                let uu____7665 =
                                  let uu____7671 =
                                    let uu____7672 =
                                      let uu____7673 =
                                        let uu____7676 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7677 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7676, uu____7677) in
                                      FStar_SMTEncoding_Util.mkSub uu____7673 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7672 in
                                  quant xy uu____7671 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7665) in
                              let uu____7683 =
                                let uu____7692 =
                                  let uu____7700 =
                                    let uu____7706 =
                                      let uu____7707 =
                                        let uu____7708 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7708 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7707 in
                                    quant qx uu____7706 in
                                  (FStar_Syntax_Const.op_Minus, uu____7700) in
                                let uu____7714 =
                                  let uu____7723 =
                                    let uu____7731 =
                                      let uu____7737 =
                                        let uu____7738 =
                                          let uu____7739 =
                                            let uu____7742 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7743 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7742, uu____7743) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7739 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7738 in
                                      quant xy uu____7737 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7731) in
                                  let uu____7749 =
                                    let uu____7758 =
                                      let uu____7766 =
                                        let uu____7772 =
                                          let uu____7773 =
                                            let uu____7774 =
                                              let uu____7777 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____7778 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____7777, uu____7778) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____7774 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____7773 in
                                        quant xy uu____7772 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____7766) in
                                    let uu____7784 =
                                      let uu____7793 =
                                        let uu____7801 =
                                          let uu____7807 =
                                            let uu____7808 =
                                              let uu____7809 =
                                                let uu____7812 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____7813 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____7812, uu____7813) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____7809 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____7808 in
                                          quant xy uu____7807 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____7801) in
                                      let uu____7819 =
                                        let uu____7828 =
                                          let uu____7836 =
                                            let uu____7842 =
                                              let uu____7843 =
                                                let uu____7844 =
                                                  let uu____7847 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____7848 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____7847, uu____7848) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____7844 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____7843 in
                                            quant xy uu____7842 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____7836) in
                                        let uu____7854 =
                                          let uu____7863 =
                                            let uu____7871 =
                                              let uu____7877 =
                                                let uu____7878 =
                                                  let uu____7879 =
                                                    let uu____7882 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____7883 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____7882, uu____7883) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____7879 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____7878 in
                                              quant xy uu____7877 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____7871) in
                                          let uu____7889 =
                                            let uu____7898 =
                                              let uu____7906 =
                                                let uu____7912 =
                                                  let uu____7913 =
                                                    let uu____7914 =
                                                      let uu____7917 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____7918 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____7917,
                                                        uu____7918) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____7914 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____7913 in
                                                quant xy uu____7912 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____7906) in
                                            let uu____7924 =
                                              let uu____7933 =
                                                let uu____7941 =
                                                  let uu____7947 =
                                                    let uu____7948 =
                                                      let uu____7949 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____7949 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____7948 in
                                                  quant qx uu____7947 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____7941) in
                                              [uu____7933] in
                                            uu____7898 :: uu____7924 in
                                          uu____7863 :: uu____7889 in
                                        uu____7828 :: uu____7854 in
                                      uu____7793 :: uu____7819 in
                                    uu____7758 :: uu____7784 in
                                  uu____7723 :: uu____7749 in
                                uu____7692 :: uu____7714 in
                              uu____7657 :: uu____7683 in
                            uu____7622 :: uu____7648 in
                          uu____7587 :: uu____7613 in
                        uu____7552 :: uu____7578 in
                      uu____7517 :: uu____7543 in
                    uu____7486 :: uu____7508 in
                  uu____7456 :: uu____7477 in
                let mk1 l v1 =
                  let uu____8077 =
                    let uu____8082 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8114  ->
                              match uu____8114 with
                              | (l',uu____8123) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8082
                      (FStar_Option.map
                         (fun uu____8156  ->
                            match uu____8156 with | (uu____8167,b) -> b v1)) in
                  FStar_All.pipe_right uu____8077 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8208  ->
                          match uu____8208 with
                          | (l',uu____8217) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8243 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8243 with
        | (xxsym,xx) ->
            let uu____8248 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8248 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8256 =
                   let uu____8260 =
                     let uu____8261 =
                       let uu____8267 =
                         let uu____8268 =
                           let uu____8271 =
                             let uu____8272 =
                               let uu____8275 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8275) in
                             FStar_SMTEncoding_Util.mkEq uu____8272 in
                           (xx_has_type, uu____8271) in
                         FStar_SMTEncoding_Util.mkImp uu____8268 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8267) in
                     FStar_SMTEncoding_Util.mkForall uu____8261 in
                   let uu____8288 =
                     let uu____8289 =
                       let uu____8290 =
                         let uu____8291 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8291 in
                       Prims.strcat module_name uu____8290 in
                     varops.mk_unique uu____8289 in
                   (uu____8260, (Some "pretyping"), uu____8288) in
                 FStar_SMTEncoding_Util.mkAssume uu____8256)
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
    let uu____8321 =
      let uu____8322 =
        let uu____8326 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8326, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8322 in
    let uu____8328 =
      let uu____8330 =
        let uu____8331 =
          let uu____8335 =
            let uu____8336 =
              let uu____8342 =
                let uu____8343 =
                  let uu____8346 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8346) in
                FStar_SMTEncoding_Util.mkImp uu____8343 in
              ([[typing_pred]], [xx], uu____8342) in
            mkForall_fuel uu____8336 in
          (uu____8335, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8331 in
      [uu____8330] in
    uu____8321 :: uu____8328 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8374 =
      let uu____8375 =
        let uu____8379 =
          let uu____8380 =
            let uu____8386 =
              let uu____8389 =
                let uu____8391 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8391] in
              [uu____8389] in
            let uu____8394 =
              let uu____8395 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8395 tt in
            (uu____8386, [bb], uu____8394) in
          FStar_SMTEncoding_Util.mkForall uu____8380 in
        (uu____8379, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8375 in
    let uu____8406 =
      let uu____8408 =
        let uu____8409 =
          let uu____8413 =
            let uu____8414 =
              let uu____8420 =
                let uu____8421 =
                  let uu____8424 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8424) in
                FStar_SMTEncoding_Util.mkImp uu____8421 in
              ([[typing_pred]], [xx], uu____8420) in
            mkForall_fuel uu____8414 in
          (uu____8413, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8409 in
      [uu____8408] in
    uu____8374 :: uu____8406 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8458 =
        let uu____8459 =
          let uu____8463 =
            let uu____8465 =
              let uu____8467 =
                let uu____8469 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8470 =
                  let uu____8472 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8472] in
                uu____8469 :: uu____8470 in
              tt :: uu____8467 in
            tt :: uu____8465 in
          ("Prims.Precedes", uu____8463) in
        FStar_SMTEncoding_Util.mkApp uu____8459 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8458 in
    let precedes_y_x =
      let uu____8475 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8475 in
    let uu____8477 =
      let uu____8478 =
        let uu____8482 =
          let uu____8483 =
            let uu____8489 =
              let uu____8492 =
                let uu____8494 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8494] in
              [uu____8492] in
            let uu____8497 =
              let uu____8498 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8498 tt in
            (uu____8489, [bb], uu____8497) in
          FStar_SMTEncoding_Util.mkForall uu____8483 in
        (uu____8482, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8478 in
    let uu____8509 =
      let uu____8511 =
        let uu____8512 =
          let uu____8516 =
            let uu____8517 =
              let uu____8523 =
                let uu____8524 =
                  let uu____8527 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8527) in
                FStar_SMTEncoding_Util.mkImp uu____8524 in
              ([[typing_pred]], [xx], uu____8523) in
            mkForall_fuel uu____8517 in
          (uu____8516, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8512 in
      let uu____8540 =
        let uu____8542 =
          let uu____8543 =
            let uu____8547 =
              let uu____8548 =
                let uu____8554 =
                  let uu____8555 =
                    let uu____8558 =
                      let uu____8559 =
                        let uu____8561 =
                          let uu____8563 =
                            let uu____8565 =
                              let uu____8566 =
                                let uu____8569 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8570 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8569, uu____8570) in
                              FStar_SMTEncoding_Util.mkGT uu____8566 in
                            let uu____8571 =
                              let uu____8573 =
                                let uu____8574 =
                                  let uu____8577 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8578 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8577, uu____8578) in
                                FStar_SMTEncoding_Util.mkGTE uu____8574 in
                              let uu____8579 =
                                let uu____8581 =
                                  let uu____8582 =
                                    let uu____8585 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8586 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8585, uu____8586) in
                                  FStar_SMTEncoding_Util.mkLT uu____8582 in
                                [uu____8581] in
                              uu____8573 :: uu____8579 in
                            uu____8565 :: uu____8571 in
                          typing_pred_y :: uu____8563 in
                        typing_pred :: uu____8561 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8559 in
                    (uu____8558, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8555 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8554) in
              mkForall_fuel uu____8548 in
            (uu____8547, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8543 in
        [uu____8542] in
      uu____8511 :: uu____8540 in
    uu____8477 :: uu____8509 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8616 =
      let uu____8617 =
        let uu____8621 =
          let uu____8622 =
            let uu____8628 =
              let uu____8631 =
                let uu____8633 = FStar_SMTEncoding_Term.boxString b in
                [uu____8633] in
              [uu____8631] in
            let uu____8636 =
              let uu____8637 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8637 tt in
            (uu____8628, [bb], uu____8636) in
          FStar_SMTEncoding_Util.mkForall uu____8622 in
        (uu____8621, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8617 in
    let uu____8648 =
      let uu____8650 =
        let uu____8651 =
          let uu____8655 =
            let uu____8656 =
              let uu____8662 =
                let uu____8663 =
                  let uu____8666 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8666) in
                FStar_SMTEncoding_Util.mkImp uu____8663 in
              ([[typing_pred]], [xx], uu____8662) in
            mkForall_fuel uu____8656 in
          (uu____8655, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8651 in
      [uu____8650] in
    uu____8616 :: uu____8648 in
  let mk_ref1 env reft_name uu____8688 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8699 =
        let uu____8703 =
          let uu____8705 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8705] in
        (reft_name, uu____8703) in
      FStar_SMTEncoding_Util.mkApp uu____8699 in
    let refb =
      let uu____8708 =
        let uu____8712 =
          let uu____8714 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8714] in
        (reft_name, uu____8712) in
      FStar_SMTEncoding_Util.mkApp uu____8708 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8718 =
      let uu____8719 =
        let uu____8723 =
          let uu____8724 =
            let uu____8730 =
              let uu____8731 =
                let uu____8734 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8734) in
              FStar_SMTEncoding_Util.mkImp uu____8731 in
            ([[typing_pred]], [xx; aa], uu____8730) in
          mkForall_fuel uu____8724 in
        (uu____8723, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8719 in
    [uu____8718] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____8774 =
      let uu____8775 =
        let uu____8779 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____8779, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8775 in
    [uu____8774] in
  let mk_and_interp env conj uu____8790 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8807 =
      let uu____8808 =
        let uu____8812 =
          let uu____8813 =
            let uu____8819 =
              let uu____8820 =
                let uu____8823 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____8823, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8820 in
            ([[l_and_a_b]], [aa; bb], uu____8819) in
          FStar_SMTEncoding_Util.mkForall uu____8813 in
        (uu____8812, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8808 in
    [uu____8807] in
  let mk_or_interp env disj uu____8847 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____8864 =
      let uu____8865 =
        let uu____8869 =
          let uu____8870 =
            let uu____8876 =
              let uu____8877 =
                let uu____8880 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____8880, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8877 in
            ([[l_or_a_b]], [aa; bb], uu____8876) in
          FStar_SMTEncoding_Util.mkForall uu____8870 in
        (uu____8869, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8865 in
    [uu____8864] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____8921 =
      let uu____8922 =
        let uu____8926 =
          let uu____8927 =
            let uu____8933 =
              let uu____8934 =
                let uu____8937 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____8937, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8934 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____8933) in
          FStar_SMTEncoding_Util.mkForall uu____8927 in
        (uu____8926, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8922 in
    [uu____8921] in
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
    let uu____8984 =
      let uu____8985 =
        let uu____8989 =
          let uu____8990 =
            let uu____8996 =
              let uu____8997 =
                let uu____9000 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9000, valid) in
              FStar_SMTEncoding_Util.mkIff uu____8997 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____8996) in
          FStar_SMTEncoding_Util.mkForall uu____8990 in
        (uu____8989, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____8985 in
    [uu____8984] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9045 =
      let uu____9046 =
        let uu____9050 =
          let uu____9051 =
            let uu____9057 =
              let uu____9058 =
                let uu____9061 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9061, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9058 in
            ([[l_imp_a_b]], [aa; bb], uu____9057) in
          FStar_SMTEncoding_Util.mkForall uu____9051 in
        (uu____9050, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9046 in
    [uu____9045] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9102 =
      let uu____9103 =
        let uu____9107 =
          let uu____9108 =
            let uu____9114 =
              let uu____9115 =
                let uu____9118 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9118, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9115 in
            ([[l_iff_a_b]], [aa; bb], uu____9114) in
          FStar_SMTEncoding_Util.mkForall uu____9108 in
        (uu____9107, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9103 in
    [uu____9102] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9152 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9152 in
    let uu____9154 =
      let uu____9155 =
        let uu____9159 =
          let uu____9160 =
            let uu____9166 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9166) in
          FStar_SMTEncoding_Util.mkForall uu____9160 in
        (uu____9159, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9155 in
    [uu____9154] in
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
      let uu____9206 =
        let uu____9210 =
          let uu____9212 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9212] in
        ("Valid", uu____9210) in
      FStar_SMTEncoding_Util.mkApp uu____9206 in
    let uu____9214 =
      let uu____9215 =
        let uu____9219 =
          let uu____9220 =
            let uu____9226 =
              let uu____9227 =
                let uu____9230 =
                  let uu____9231 =
                    let uu____9237 =
                      let uu____9240 =
                        let uu____9242 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9242] in
                      [uu____9240] in
                    let uu____9245 =
                      let uu____9246 =
                        let uu____9249 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9249, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9246 in
                    (uu____9237, [xx1], uu____9245) in
                  FStar_SMTEncoding_Util.mkForall uu____9231 in
                (uu____9230, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9227 in
            ([[l_forall_a_b]], [aa; bb], uu____9226) in
          FStar_SMTEncoding_Util.mkForall uu____9220 in
        (uu____9219, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9215 in
    [uu____9214] in
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
      let uu____9300 =
        let uu____9304 =
          let uu____9306 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9306] in
        ("Valid", uu____9304) in
      FStar_SMTEncoding_Util.mkApp uu____9300 in
    let uu____9308 =
      let uu____9309 =
        let uu____9313 =
          let uu____9314 =
            let uu____9320 =
              let uu____9321 =
                let uu____9324 =
                  let uu____9325 =
                    let uu____9331 =
                      let uu____9334 =
                        let uu____9336 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9336] in
                      [uu____9334] in
                    let uu____9339 =
                      let uu____9340 =
                        let uu____9343 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9343, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9340 in
                    (uu____9331, [xx1], uu____9339) in
                  FStar_SMTEncoding_Util.mkExists uu____9325 in
                (uu____9324, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9321 in
            ([[l_exists_a_b]], [aa; bb], uu____9320) in
          FStar_SMTEncoding_Util.mkForall uu____9314 in
        (uu____9313, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9309 in
    [uu____9308] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9379 =
      let uu____9380 =
        let uu____9384 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9385 = varops.mk_unique "typing_range_const" in
        (uu____9384, (Some "Range_const typing"), uu____9385) in
      FStar_SMTEncoding_Util.mkAssume uu____9380 in
    [uu____9379] in
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
          let uu____9647 =
            FStar_Util.find_opt
              (fun uu____9665  ->
                 match uu____9665 with
                 | (l,uu____9675) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9647 with
          | None  -> []
          | Some (uu____9697,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9734 = encode_function_type_as_formula None None t env in
        match uu____9734 with
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
            let uu____9766 =
              (let uu____9767 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____9767) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____9766
            then
              let uu____9771 = new_term_constant_and_tok_from_lid env lid in
              match uu____9771 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____9783 =
                      let uu____9784 = FStar_Syntax_Subst.compress t_norm in
                      uu____9784.FStar_Syntax_Syntax.n in
                    match uu____9783 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____9789) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____9806  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____9809 -> [] in
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
              (let uu____9818 = prims.is lid in
               if uu____9818
               then
                 let vname = varops.new_fvar lid in
                 let uu____9823 = prims.mk lid vname in
                 match uu____9823 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____9838 =
                    let uu____9844 = curried_arrow_formals_comp t_norm in
                    match uu____9844 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____9855 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____9855
                          then
                            let uu____9856 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___148_9857 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___148_9857.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___148_9857.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___148_9857.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___148_9857.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___148_9857.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___148_9857.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___148_9857.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___148_9857.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___148_9857.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___148_9857.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___148_9857.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___148_9857.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___148_9857.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___148_9857.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___148_9857.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___148_9857.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___148_9857.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___148_9857.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___148_9857.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___148_9857.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___148_9857.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___148_9857.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___148_9857.FStar_TypeChecker_Env.qname_and_index);
                                   FStar_TypeChecker_Env.proof_ns =
                                     (uu___148_9857.FStar_TypeChecker_Env.proof_ns)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____9856
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____9864 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____9864)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____9838 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____9891 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____9891 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____9904 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___119_9928  ->
                                     match uu___119_9928 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____9931 =
                                           FStar_Util.prefix vars in
                                         (match uu____9931 with
                                          | (uu____9942,(xxsym,uu____9944))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____9954 =
                                                let uu____9955 =
                                                  let uu____9959 =
                                                    let uu____9960 =
                                                      let uu____9966 =
                                                        let uu____9967 =
                                                          let uu____9970 =
                                                            let uu____9971 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____9971 in
                                                          (vapp, uu____9970) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____9967 in
                                                      ([[vapp]], vars,
                                                        uu____9966) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____9960 in
                                                  (uu____9959,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____9955 in
                                              [uu____9954])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____9982 =
                                           FStar_Util.prefix vars in
                                         (match uu____9982 with
                                          | (uu____9993,(xxsym,uu____9995))
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
                                              let uu____10009 =
                                                let uu____10010 =
                                                  let uu____10014 =
                                                    let uu____10015 =
                                                      let uu____10021 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10021) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10015 in
                                                  (uu____10014,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10010 in
                                              [uu____10009])
                                     | uu____10030 -> [])) in
                           let uu____10031 = encode_binders None formals env1 in
                           (match uu____10031 with
                            | (vars,guards,env',decls1,uu____10047) ->
                                let uu____10054 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10059 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10059, decls1)
                                  | Some p ->
                                      let uu____10061 = encode_formula p env' in
                                      (match uu____10061 with
                                       | (g,ds) ->
                                           let uu____10068 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10068,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10054 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10077 =
                                         let uu____10081 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10081) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10077 in
                                     let uu____10086 =
                                       let vname_decl =
                                         let uu____10091 =
                                           let uu____10097 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10102  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10097,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10091 in
                                       let uu____10107 =
                                         let env2 =
                                           let uu___149_10111 = env1 in
                                           {
                                             bindings =
                                               (uu___149_10111.bindings);
                                             depth = (uu___149_10111.depth);
                                             tcenv = (uu___149_10111.tcenv);
                                             warn = (uu___149_10111.warn);
                                             cache = (uu___149_10111.cache);
                                             nolabels =
                                               (uu___149_10111.nolabels);
                                             use_zfuel_name =
                                               (uu___149_10111.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___149_10111.current_module_name)
                                           } in
                                         let uu____10112 =
                                           let uu____10113 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10113 in
                                         if uu____10112
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10107 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10123::uu____10124 ->
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
                                                   let uu____10147 =
                                                     let uu____10153 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10153) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10147 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10167 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10169 =
                                             match formals with
                                             | [] ->
                                                 let uu____10178 =
                                                   let uu____10179 =
                                                     let uu____10181 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_33  ->
                                                          Some _0_33)
                                                       uu____10181 in
                                                   push_free_var env1 lid
                                                     vname uu____10179 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10178)
                                             | uu____10184 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10189 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10189 in
                                                 let name_tok_corr =
                                                   let uu____10191 =
                                                     let uu____10195 =
                                                       let uu____10196 =
                                                         let uu____10202 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10202) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10196 in
                                                     (uu____10195,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10191 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10169 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10086 with
                                      | (decls2,env2) ->
                                          let uu____10226 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10231 =
                                              encode_term res_t1 env' in
                                            match uu____10231 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10239 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10239,
                                                  decls) in
                                          (match uu____10226 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10247 =
                                                   let uu____10251 =
                                                     let uu____10252 =
                                                       let uu____10258 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10258) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10252 in
                                                   (uu____10251,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10247 in
                                               let freshness =
                                                 let uu____10267 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10267
                                                 then
                                                   let uu____10270 =
                                                     let uu____10271 =
                                                       let uu____10277 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              Prims.snd) in
                                                       let uu____10283 =
                                                         varops.next_id () in
                                                       (vname, uu____10277,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10283) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10271 in
                                                   let uu____10285 =
                                                     let uu____10287 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10287] in
                                                   uu____10270 :: uu____10285
                                                 else [] in
                                               let g =
                                                 let uu____10291 =
                                                   let uu____10293 =
                                                     let uu____10295 =
                                                       let uu____10297 =
                                                         let uu____10299 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10299 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10297 in
                                                     FStar_List.append decls3
                                                       uu____10295 in
                                                   FStar_List.append decls2
                                                     uu____10293 in
                                                 FStar_List.append decls11
                                                   uu____10291 in
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
          let uu____10321 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10321 with
          | None  ->
              let uu____10344 = encode_free_var env x t t_norm [] in
              (match uu____10344 with
               | (decls,env1) ->
                   let uu____10359 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10359 with
                    | (n1,x',uu____10378) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10390) -> ((n1, x1), [], env)
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
          let uu____10423 = encode_free_var env lid t tt quals in
          match uu____10423 with
          | (decls,env1) ->
              let uu____10434 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10434
              then
                let uu____10438 =
                  let uu____10440 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10440 in
                (uu____10438, env1)
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
             (fun uu____10468  ->
                fun lb  ->
                  match uu____10468 with
                  | (decls,env1) ->
                      let uu____10480 =
                        let uu____10484 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10484
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10480 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10498 = FStar_Syntax_Util.head_and_args t in
    match uu____10498 with
    | (hd1,args) ->
        let uu____10524 =
          let uu____10525 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10525.FStar_Syntax_Syntax.n in
        (match uu____10524 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10529,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10542 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10557  ->
      fun quals  ->
        match uu____10557 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10606 = FStar_Util.first_N nbinders formals in
              match uu____10606 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10646  ->
                         fun uu____10647  ->
                           match (uu____10646, uu____10647) with
                           | ((formal,uu____10657),(binder,uu____10659)) ->
                               let uu____10664 =
                                 let uu____10669 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10669) in
                               FStar_Syntax_Syntax.NT uu____10664) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10674 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10688  ->
                              match uu____10688 with
                              | (x,i) ->
                                  let uu____10695 =
                                    let uu___150_10696 = x in
                                    let uu____10697 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___150_10696.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___150_10696.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10697
                                    } in
                                  (uu____10695, i))) in
                    FStar_All.pipe_right uu____10674
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10709 =
                      let uu____10711 =
                        let uu____10712 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10712.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_34  -> Some _0_34)
                        uu____10711 in
                    let uu____10716 =
                      let uu____10717 = FStar_Syntax_Subst.compress body in
                      let uu____10718 =
                        let uu____10719 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left Prims.snd uu____10719 in
                      FStar_Syntax_Syntax.extend_app_n uu____10717
                        uu____10718 in
                    uu____10716 uu____10709 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____10761 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____10761
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___151_10762 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___151_10762.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___151_10762.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___151_10762.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___151_10762.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___151_10762.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___151_10762.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___151_10762.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___151_10762.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___151_10762.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___151_10762.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___151_10762.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___151_10762.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___151_10762.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___151_10762.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___151_10762.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___151_10762.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___151_10762.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___151_10762.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___151_10762.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___151_10762.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___151_10762.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___151_10762.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___151_10762.FStar_TypeChecker_Env.qname_and_index);
                       FStar_TypeChecker_Env.proof_ns =
                         (uu___151_10762.FStar_TypeChecker_Env.proof_ns)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____10783 = FStar_Syntax_Util.abs_formals e in
                match uu____10783 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____10832::uu____10833 ->
                         let uu____10841 =
                           let uu____10842 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____10842.FStar_Syntax_Syntax.n in
                         (match uu____10841 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____10869 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____10869 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____10895 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____10895
                                   then
                                     let uu____10913 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____10913 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____10959  ->
                                                   fun uu____10960  ->
                                                     match (uu____10959,
                                                             uu____10960)
                                                     with
                                                     | ((x,uu____10970),
                                                        (b,uu____10972)) ->
                                                         let uu____10977 =
                                                           let uu____10982 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____10982) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____10977)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____10984 =
                                            let uu____10995 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____10995) in
                                          (uu____10984, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11030 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11030 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11082) ->
                              let uu____11087 =
                                let uu____11098 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                Prims.fst uu____11098 in
                              (uu____11087, true)
                          | uu____11131 when Prims.op_Negation norm1 ->
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
                          | uu____11133 ->
                              let uu____11134 =
                                let uu____11135 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11136 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11135
                                  uu____11136 in
                              failwith uu____11134)
                     | uu____11149 ->
                         let uu____11150 =
                           let uu____11151 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11151.FStar_Syntax_Syntax.n in
                         (match uu____11150 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11178 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11178 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11196 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11196 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11244 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11272 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11272
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11279 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11320  ->
                            fun lb  ->
                              match uu____11320 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11371 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11371
                                    then Prims.raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11374 =
                                      let uu____11382 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11382
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11374 with
                                    | (tok,decl,env2) ->
                                        let uu____11407 =
                                          let uu____11414 =
                                            let uu____11420 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11420, tok) in
                                          uu____11414 :: toks in
                                        (uu____11407, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11279 with
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
                        | uu____11522 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11527 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11527 vars)
                            else
                              (let uu____11529 =
                                 let uu____11533 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11533) in
                               FStar_SMTEncoding_Util.mkApp uu____11529) in
                      let uu____11538 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___120_11540  ->
                                 match uu___120_11540 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11541 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11544 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11544))) in
                      if uu____11538
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11564;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11566;
                                FStar_Syntax_Syntax.lbeff = uu____11567;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11608 =
                                 let uu____11612 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11612 with
                                 | (tcenv',uu____11623,e_t) ->
                                     let uu____11627 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11634 -> failwith "Impossible" in
                                     (match uu____11627 with
                                      | (e1,t_norm1) ->
                                          ((let uu___154_11643 = env1 in
                                            {
                                              bindings =
                                                (uu___154_11643.bindings);
                                              depth = (uu___154_11643.depth);
                                              tcenv = tcenv';
                                              warn = (uu___154_11643.warn);
                                              cache = (uu___154_11643.cache);
                                              nolabels =
                                                (uu___154_11643.nolabels);
                                              use_zfuel_name =
                                                (uu___154_11643.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___154_11643.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___154_11643.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11608 with
                                | (env',e1,t_norm1) ->
                                    let uu____11650 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11650 with
                                     | ((binders,body,uu____11662,uu____11663),curry)
                                         ->
                                         ((let uu____11670 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11670
                                           then
                                             let uu____11671 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11672 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11671 uu____11672
                                           else ());
                                          (let uu____11674 =
                                             encode_binders None binders env' in
                                           match uu____11674 with
                                           | (vars,guards,env'1,binder_decls,uu____11690)
                                               ->
                                               let body1 =
                                                 let uu____11698 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11698
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11701 =
                                                 let uu____11706 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11706
                                                 then
                                                   let uu____11712 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11713 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11712, uu____11713)
                                                 else
                                                   (let uu____11719 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11719)) in
                                               (match uu____11701 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11733 =
                                                        let uu____11737 =
                                                          let uu____11738 =
                                                            let uu____11744 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11744) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11738 in
                                                        let uu____11750 =
                                                          let uu____11752 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11752 in
                                                        (uu____11737,
                                                          uu____11750,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11733 in
                                                    let uu____11754 =
                                                      let uu____11756 =
                                                        let uu____11758 =
                                                          let uu____11760 =
                                                            let uu____11762 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____11762 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____11760 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____11758 in
                                                      FStar_List.append
                                                        decls1 uu____11756 in
                                                    (uu____11754, env1))))))
                           | uu____11765 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____11784 = varops.fresh "fuel" in
                             (uu____11784, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____11787 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____11826  ->
                                     fun uu____11827  ->
                                       match (uu____11826, uu____11827) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____11909 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____11909 in
                                           let gtok =
                                             let uu____11911 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____11911 in
                                           let env3 =
                                             let uu____11913 =
                                               let uu____11915 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_35  -> Some _0_35)
                                                 uu____11915 in
                                             push_free_var env2 flid gtok
                                               uu____11913 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____11787 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12001
                                 t_norm uu____12003 =
                                 match (uu____12001, uu____12003) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12030;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12031;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12048 =
                                       let uu____12052 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12052 with
                                       | (tcenv',uu____12067,e_t) ->
                                           let uu____12071 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12078 ->
                                                 failwith "Impossible" in
                                           (match uu____12071 with
                                            | (e1,t_norm1) ->
                                                ((let uu___155_12087 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___155_12087.bindings);
                                                    depth =
                                                      (uu___155_12087.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___155_12087.warn);
                                                    cache =
                                                      (uu___155_12087.cache);
                                                    nolabels =
                                                      (uu___155_12087.nolabels);
                                                    use_zfuel_name =
                                                      (uu___155_12087.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___155_12087.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___155_12087.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12048 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12097 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12097
                                            then
                                              let uu____12098 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12099 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12100 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12098 uu____12099
                                                uu____12100
                                            else ());
                                           (let uu____12102 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12102 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12124 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12124
                                                  then
                                                    let uu____12125 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12126 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12127 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12128 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12125 uu____12126
                                                      uu____12127 uu____12128
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12132 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12132 with
                                                  | (vars,guards,env'1,binder_decls,uu____12150)
                                                      ->
                                                      let decl_g =
                                                        let uu____12158 =
                                                          let uu____12164 =
                                                            let uu____12166 =
                                                              FStar_List.map
                                                                Prims.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12166 in
                                                          (g, uu____12164,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12158 in
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
                                                        let uu____12181 =
                                                          let uu____12185 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12185) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12181 in
                                                      let gsapp =
                                                        let uu____12191 =
                                                          let uu____12195 =
                                                            let uu____12197 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12197 ::
                                                              vars_tm in
                                                          (g, uu____12195) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12191 in
                                                      let gmax =
                                                        let uu____12201 =
                                                          let uu____12205 =
                                                            let uu____12207 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12207 ::
                                                              vars_tm in
                                                          (g, uu____12205) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12201 in
                                                      let body1 =
                                                        let uu____12211 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12211
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12213 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12213 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12224
                                                               =
                                                               let uu____12228
                                                                 =
                                                                 let uu____12229
                                                                   =
                                                                   let uu____12237
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
                                                                    uu____12237) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12229 in
                                                               let uu____12248
                                                                 =
                                                                 let uu____12250
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12250 in
                                                               (uu____12228,
                                                                 uu____12248,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12224 in
                                                           let eqn_f =
                                                             let uu____12253
                                                               =
                                                               let uu____12257
                                                                 =
                                                                 let uu____12258
                                                                   =
                                                                   let uu____12264
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12264) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12258 in
                                                               (uu____12257,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12253 in
                                                           let eqn_g' =
                                                             let uu____12272
                                                               =
                                                               let uu____12276
                                                                 =
                                                                 let uu____12277
                                                                   =
                                                                   let uu____12283
                                                                    =
                                                                    let uu____12284
                                                                    =
                                                                    let uu____12287
                                                                    =
                                                                    let uu____12288
                                                                    =
                                                                    let uu____12292
                                                                    =
                                                                    let uu____12294
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12294
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12292) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12288 in
                                                                    (gsapp,
                                                                    uu____12287) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12284 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12283) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12277 in
                                                               (uu____12276,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12272 in
                                                           let uu____12306 =
                                                             let uu____12311
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12311
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12328)
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
                                                                    let uu____12343
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12343
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12346
                                                                    =
                                                                    let uu____12350
                                                                    =
                                                                    let uu____12351
                                                                    =
                                                                    let uu____12357
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12357) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12351 in
                                                                    (uu____12350,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12346 in
                                                                 let uu____12368
                                                                   =
                                                                   let uu____12372
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12372
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12380
                                                                    =
                                                                    let uu____12382
                                                                    =
                                                                    let uu____12383
                                                                    =
                                                                    let uu____12387
                                                                    =
                                                                    let uu____12388
                                                                    =
                                                                    let uu____12394
                                                                    =
                                                                    let uu____12395
                                                                    =
                                                                    let uu____12398
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12398,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12395 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12394) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12388 in
                                                                    (uu____12387,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12383 in
                                                                    [uu____12382] in
                                                                    (d3,
                                                                    uu____12380) in
                                                                 (match uu____12368
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12306
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
                               let uu____12433 =
                                 let uu____12440 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12476  ->
                                      fun uu____12477  ->
                                        match (uu____12476, uu____12477) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12563 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12563 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12440 in
                               (match uu____12433 with
                                | (decls2,eqns,env01) ->
                                    let uu____12603 =
                                      let isDeclFun uu___121_12611 =
                                        match uu___121_12611 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12612 -> true
                                        | uu____12618 -> false in
                                      let uu____12619 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12619
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12603 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12646 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12646
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
        let uu____12679 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12679 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12682 = encode_sigelt' env se in
      match uu____12682 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12692 =
                  let uu____12693 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12693 in
                [uu____12692]
            | uu____12694 ->
                let uu____12695 =
                  let uu____12697 =
                    let uu____12698 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12698 in
                  uu____12697 :: g in
                let uu____12699 =
                  let uu____12701 =
                    let uu____12702 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12702 in
                  [uu____12701] in
                FStar_List.append uu____12695 uu____12699 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12710 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12719 =
            let uu____12720 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12720 Prims.op_Negation in
          if uu____12719
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12740 ->
                   let uu____12741 =
                     let uu____12744 =
                       let uu____12745 =
                         let uu____12760 =
                           FStar_All.pipe_left (fun _0_36  -> Some _0_36)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____12760) in
                       FStar_Syntax_Syntax.Tm_abs uu____12745 in
                     FStar_Syntax_Syntax.mk uu____12744 in
                   uu____12741 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____12813 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____12813 with
               | (aname,atok,env2) ->
                   let uu____12823 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____12823 with
                    | (formals,uu____12833) ->
                        let uu____12840 =
                          let uu____12843 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____12843 env2 in
                        (match uu____12840 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____12851 =
                                 let uu____12852 =
                                   let uu____12858 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____12866  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____12858,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____12852 in
                               [uu____12851;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____12873 =
                               let aux uu____12902 uu____12903 =
                                 match (uu____12902, uu____12903) with
                                 | ((bv,uu____12930),(env3,acc_sorts,acc)) ->
                                     let uu____12951 = gen_term_var env3 bv in
                                     (match uu____12951 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____12873 with
                              | (uu____12989,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13003 =
                                      let uu____13007 =
                                        let uu____13008 =
                                          let uu____13014 =
                                            let uu____13015 =
                                              let uu____13018 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13018) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13015 in
                                          ([[app]], xs_sorts, uu____13014) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13008 in
                                      (uu____13007, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13003 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13030 =
                                      let uu____13034 =
                                        let uu____13035 =
                                          let uu____13041 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13041) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13035 in
                                      (uu____13034,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13030 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13051 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13051 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13067,uu____13068)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13069 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13069 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13080,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13085 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___122_13087  ->
                      match uu___122_13087 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13090 -> false)) in
            Prims.op_Negation uu____13085 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13096 = encode_top_level_val env fv t quals in
             match uu____13096 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13108 =
                   let uu____13110 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13110 in
                 (uu____13108, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13115 = encode_formula f env in
          (match uu____13115 with
           | (f1,decls) ->
               let g =
                 let uu____13124 =
                   let uu____13125 =
                     let uu____13129 =
                       let uu____13131 =
                         let uu____13132 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13132 in
                       Some uu____13131 in
                     let uu____13133 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13129, uu____13133) in
                   FStar_SMTEncoding_Util.mkAssume uu____13125 in
                 [uu____13124] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13137,uu____13138) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13144 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13151 =
                       let uu____13156 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13156.FStar_Syntax_Syntax.fv_name in
                     uu____13151.FStar_Syntax_Syntax.v in
                   let uu____13160 =
                     let uu____13161 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13161 in
                   if uu____13160
                   then
                     let val_decl =
                       let uu___156_13176 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___156_13176.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___156_13176.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___156_13176.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13180 = encode_sigelt' env1 val_decl in
                     match uu____13180 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (Prims.snd lbs) in
          (match uu____13144 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13197,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13199;
                          FStar_Syntax_Syntax.lbtyp = uu____13200;
                          FStar_Syntax_Syntax.lbeff = uu____13201;
                          FStar_Syntax_Syntax.lbdef = uu____13202;_}::[]),uu____13203,uu____13204)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13218 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13218 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13241 =
                   let uu____13243 =
                     let uu____13244 =
                       let uu____13248 =
                         let uu____13249 =
                           let uu____13255 =
                             let uu____13256 =
                               let uu____13259 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13259) in
                             FStar_SMTEncoding_Util.mkEq uu____13256 in
                           ([[b2t_x]], [xx], uu____13255) in
                         FStar_SMTEncoding_Util.mkForall uu____13249 in
                       (uu____13248, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13244 in
                   [uu____13243] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13241 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13276,uu____13277,uu____13278)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___123_13284  ->
                  match uu___123_13284 with
                  | FStar_Syntax_Syntax.Discriminator uu____13285 -> true
                  | uu____13286 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13288,lids,uu____13290) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13297 =
                     let uu____13298 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13298.FStar_Ident.idText in
                   uu____13297 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___124_13300  ->
                     match uu___124_13300 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13301 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13304,uu____13305)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___125_13315  ->
                  match uu___125_13315 with
                  | FStar_Syntax_Syntax.Projector uu____13316 -> true
                  | uu____13319 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13326 = try_lookup_free_var env l in
          (match uu____13326 with
           | Some uu____13330 -> ([], env)
           | None  ->
               let se1 =
                 let uu___157_13333 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___157_13333.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___157_13333.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13339,uu____13340) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13352) ->
          let uu____13357 = encode_sigelts env ses in
          (match uu____13357 with
           | (g,env1) ->
               let uu____13367 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___126_13377  ->
                         match uu___126_13377 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13378;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13379;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13380;_}
                             -> false
                         | uu____13382 -> true)) in
               (match uu____13367 with
                | (g',inversions) ->
                    let uu____13391 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___127_13401  ->
                              match uu___127_13401 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13402 ->
                                  true
                              | uu____13408 -> false)) in
                    (match uu____13391 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13419,tps,k,uu____13422,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___128_13432  ->
                    match uu___128_13432 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13433 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13440 = c in
              match uu____13440 with
              | (name,args,uu____13444,uu____13445,uu____13446) ->
                  let uu____13449 =
                    let uu____13450 =
                      let uu____13456 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13463  ->
                                match uu____13463 with
                                | (uu____13467,sort,uu____13469) -> sort)) in
                      (name, uu____13456, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13450 in
                  [uu____13449]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13487 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13490 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13490 FStar_Option.isNone)) in
            if uu____13487
            then []
            else
              (let uu____13507 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13507 with
               | (xxsym,xx) ->
                   let uu____13513 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13524  ->
                             fun l  ->
                               match uu____13524 with
                               | (out,decls) ->
                                   let uu____13536 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13536 with
                                    | (uu____13542,data_t) ->
                                        let uu____13544 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13544 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13573 =
                                                 let uu____13574 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13574.FStar_Syntax_Syntax.n in
                                               match uu____13573 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13582,indices) ->
                                                   indices
                                               | uu____13598 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13610  ->
                                                         match uu____13610
                                                         with
                                                         | (x,uu____13614) ->
                                                             let uu____13615
                                                               =
                                                               let uu____13616
                                                                 =
                                                                 let uu____13620
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13620,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13616 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13615)
                                                    env) in
                                             let uu____13622 =
                                               encode_args indices env1 in
                                             (match uu____13622 with
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
                                                      let uu____13642 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13650
                                                                 =
                                                                 let uu____13653
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13653,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13650)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13642
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13655 =
                                                      let uu____13656 =
                                                        let uu____13659 =
                                                          let uu____13660 =
                                                            let uu____13663 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13663,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13660 in
                                                        (out, uu____13659) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13656 in
                                                    (uu____13655,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13513 with
                    | (data_ax,decls) ->
                        let uu____13671 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13671 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13682 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13682 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13685 =
                                 let uu____13689 =
                                   let uu____13690 =
                                     let uu____13696 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13704 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13696,
                                       uu____13704) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13690 in
                                 let uu____13712 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13689, (Some "inversion axiom"),
                                   uu____13712) in
                               FStar_SMTEncoding_Util.mkAssume uu____13685 in
                             let pattern_guarded_inversion =
                               let uu____13716 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13716
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13724 =
                                   let uu____13725 =
                                     let uu____13729 =
                                       let uu____13730 =
                                         let uu____13736 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13744 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13736, uu____13744) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13730 in
                                     let uu____13752 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13729, (Some "inversion axiom"),
                                       uu____13752) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13725 in
                                 [uu____13724]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13755 =
            let uu____13763 =
              let uu____13764 = FStar_Syntax_Subst.compress k in
              uu____13764.FStar_Syntax_Syntax.n in
            match uu____13763 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____13793 -> (tps, k) in
          (match uu____13755 with
           | (formals,res) ->
               let uu____13808 = FStar_Syntax_Subst.open_term formals res in
               (match uu____13808 with
                | (formals1,res1) ->
                    let uu____13815 = encode_binders None formals1 env in
                    (match uu____13815 with
                     | (vars,guards,env',binder_decls,uu____13830) ->
                         let uu____13837 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____13837 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____13850 =
                                  let uu____13854 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____13854) in
                                FStar_SMTEncoding_Util.mkApp uu____13850 in
                              let uu____13859 =
                                let tname_decl =
                                  let uu____13865 =
                                    let uu____13866 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____13881  ->
                                              match uu____13881 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____13889 = varops.next_id () in
                                    (tname, uu____13866,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____13889, false) in
                                  constructor_or_logic_type_decl uu____13865 in
                                let uu____13894 =
                                  match vars with
                                  | [] ->
                                      let uu____13901 =
                                        let uu____13902 =
                                          let uu____13904 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_37  -> Some _0_37)
                                            uu____13904 in
                                        push_free_var env1 t tname
                                          uu____13902 in
                                      ([], uu____13901)
                                  | uu____13908 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____13914 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____13914 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____13923 =
                                          let uu____13927 =
                                            let uu____13928 =
                                              let uu____13936 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____13936) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____13928 in
                                          (uu____13927,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____13923 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____13894 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____13859 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____13959 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____13959 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____13973 =
                                               let uu____13974 =
                                                 let uu____13978 =
                                                   let uu____13979 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____13979 in
                                                 (uu____13978,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13974 in
                                             [uu____13973]
                                           else [] in
                                         let uu____13982 =
                                           let uu____13984 =
                                             let uu____13986 =
                                               let uu____13987 =
                                                 let uu____13991 =
                                                   let uu____13992 =
                                                     let uu____13998 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____13998) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____13992 in
                                                 (uu____13991, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____13987 in
                                             [uu____13986] in
                                           FStar_List.append karr uu____13984 in
                                         FStar_List.append decls1 uu____13982 in
                                   let aux =
                                     let uu____14007 =
                                       let uu____14009 =
                                         inversion_axioms tapp vars in
                                       let uu____14011 =
                                         let uu____14013 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14013] in
                                       FStar_List.append uu____14009
                                         uu____14011 in
                                     FStar_List.append kindingAx uu____14007 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14018,uu____14019,uu____14020,uu____14021,uu____14022)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14027,t,uu____14029,n_tps,uu____14031) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14036 = new_term_constant_and_tok_from_lid env d in
          (match uu____14036 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14047 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14047 with
                | (formals,t_res) ->
                    let uu____14069 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14069 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14078 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14078 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14116 =
                                            mk_term_projector_name d x in
                                          (uu____14116,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14118 =
                                  let uu____14128 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14128, true) in
                                FStar_All.pipe_right uu____14118
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
                              let uu____14150 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14150 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14158::uu____14159 ->
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
                                         let uu____14184 =
                                           let uu____14190 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14190) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14184
                                     | uu____14203 -> tok_typing in
                                   let uu____14208 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14208 with
                                    | (vars',guards',env'',decls_formals,uu____14223)
                                        ->
                                        let uu____14230 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14230 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14249 ->
                                                   let uu____14253 =
                                                     let uu____14254 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14254 in
                                                   [uu____14253] in
                                             let encode_elim uu____14261 =
                                               let uu____14262 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14262 with
                                               | (head1,args) ->
                                                   let uu____14291 =
                                                     let uu____14292 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14292.FStar_Syntax_Syntax.n in
                                                   (match uu____14291 with
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
                                                        let uu____14310 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14310
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
                                                                 | uu____14336
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14344
                                                                    =
                                                                    let uu____14345
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14345 in
                                                                    if
                                                                    uu____14344
                                                                    then
                                                                    let uu____14352
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14352]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14354
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14367
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14367
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14389
                                                                    =
                                                                    let uu____14393
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14393 in
                                                                    (match uu____14389
                                                                    with
                                                                    | 
                                                                    (uu____14400,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14406
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14406
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14408
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14408
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
                                                             (match uu____14354
                                                              with
                                                              | (uu____14416,arg_vars,elim_eqns_or_guards,uu____14419)
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
                                                                    let uu____14438
                                                                    =
                                                                    let uu____14442
                                                                    =
                                                                    let uu____14443
                                                                    =
                                                                    let uu____14449
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14455
                                                                    =
                                                                    let uu____14456
                                                                    =
                                                                    let uu____14459
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14459) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14456 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14449,
                                                                    uu____14455) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14443 in
                                                                    (uu____14442,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14438 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14472
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14472,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14474
                                                                    =
                                                                    let uu____14478
                                                                    =
                                                                    let uu____14479
                                                                    =
                                                                    let uu____14485
                                                                    =
                                                                    let uu____14488
                                                                    =
                                                                    let uu____14490
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14490] in
                                                                    [uu____14488] in
                                                                    let uu____14493
                                                                    =
                                                                    let uu____14494
                                                                    =
                                                                    let uu____14497
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14498
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14497,
                                                                    uu____14498) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14494 in
                                                                    (uu____14485,
                                                                    [x],
                                                                    uu____14493) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14479 in
                                                                    let uu____14508
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14478,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14508) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14474
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14513
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
                                                                    (let uu____14528
                                                                    =
                                                                    let uu____14529
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14529
                                                                    dapp1 in
                                                                    [uu____14528]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14513
                                                                    FStar_List.flatten in
                                                                    let uu____14533
                                                                    =
                                                                    let uu____14537
                                                                    =
                                                                    let uu____14538
                                                                    =
                                                                    let uu____14544
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14550
                                                                    =
                                                                    let uu____14551
                                                                    =
                                                                    let uu____14554
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14554) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14551 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14544,
                                                                    uu____14550) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14538 in
                                                                    (uu____14537,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14533) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14564 ->
                                                        ((let uu____14566 =
                                                            let uu____14567 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14568 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14567
                                                              uu____14568 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14566);
                                                         ([], []))) in
                                             let uu____14571 = encode_elim () in
                                             (match uu____14571 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14583 =
                                                      let uu____14585 =
                                                        let uu____14587 =
                                                          let uu____14589 =
                                                            let uu____14591 =
                                                              let uu____14592
                                                                =
                                                                let uu____14598
                                                                  =
                                                                  let uu____14600
                                                                    =
                                                                    let uu____14601
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14601 in
                                                                  Some
                                                                    uu____14600 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14598) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14592 in
                                                            [uu____14591] in
                                                          let uu____14604 =
                                                            let uu____14606 =
                                                              let uu____14608
                                                                =
                                                                let uu____14610
                                                                  =
                                                                  let uu____14612
                                                                    =
                                                                    let uu____14614
                                                                    =
                                                                    let uu____14616
                                                                    =
                                                                    let uu____14617
                                                                    =
                                                                    let uu____14621
                                                                    =
                                                                    let uu____14622
                                                                    =
                                                                    let uu____14628
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14628) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14622 in
                                                                    (uu____14621,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14617 in
                                                                    let uu____14635
                                                                    =
                                                                    let uu____14637
                                                                    =
                                                                    let uu____14638
                                                                    =
                                                                    let uu____14642
                                                                    =
                                                                    let uu____14643
                                                                    =
                                                                    let uu____14649
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14655
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14649,
                                                                    uu____14655) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14643 in
                                                                    (uu____14642,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14638 in
                                                                    [uu____14637] in
                                                                    uu____14616
                                                                    ::
                                                                    uu____14635 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14614 in
                                                                  FStar_List.append
                                                                    uu____14612
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14610 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14608 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14606 in
                                                          FStar_List.append
                                                            uu____14589
                                                            uu____14604 in
                                                        FStar_List.append
                                                          decls3 uu____14587 in
                                                      FStar_List.append
                                                        decls2 uu____14585 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14583 in
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
           (fun uu____14676  ->
              fun se  ->
                match uu____14676 with
                | (g,env1) ->
                    let uu____14688 = encode_sigelt env1 se in
                    (match uu____14688 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14724 =
        match uu____14724 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14742 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14747 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14747
                   then
                     let uu____14748 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14749 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14750 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14748 uu____14749 uu____14750
                   else ());
                  (let uu____14752 = encode_term t1 env1 in
                   match uu____14752 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____14762 =
                         let uu____14766 =
                           let uu____14767 =
                             let uu____14768 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____14768
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____14767 in
                         new_term_constant_from_string env1 x uu____14766 in
                       (match uu____14762 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____14779 = FStar_Options.log_queries () in
                              if uu____14779
                              then
                                let uu____14781 =
                                  let uu____14782 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____14783 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____14784 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____14782 uu____14783 uu____14784 in
                                Some uu____14781
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____14795,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____14804 = encode_free_var env1 fv t t_norm [] in
                 (match uu____14804 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____14823 = encode_sigelt env1 se in
                 (match uu____14823 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____14833 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____14833 with | (uu____14845,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____14890  ->
            match uu____14890 with
            | (l,uu____14897,uu____14898) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((Prims.fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____14919  ->
            match uu____14919 with
            | (l,uu____14927,uu____14928) ->
                let uu____14933 =
                  FStar_All.pipe_left
                    (fun _0_38  -> FStar_SMTEncoding_Term.Echo _0_38)
                    (Prims.fst l) in
                let uu____14934 =
                  let uu____14936 =
                    let uu____14937 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____14937 in
                  [uu____14936] in
                uu____14933 :: uu____14934)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____14948 =
      let uu____14950 =
        let uu____14951 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____14953 =
          let uu____14954 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____14954 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____14951;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____14953
        } in
      [uu____14950] in
    FStar_ST.write last_env uu____14948
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____14964 = FStar_ST.read last_env in
      match uu____14964 with
      | [] -> failwith "No env; call init first!"
      | e::uu____14970 ->
          let uu___158_14972 = e in
          let uu____14973 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___158_14972.bindings);
            depth = (uu___158_14972.depth);
            tcenv;
            warn = (uu___158_14972.warn);
            cache = (uu___158_14972.cache);
            nolabels = (uu___158_14972.nolabels);
            use_zfuel_name = (uu___158_14972.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___158_14972.encode_non_total_function_typ);
            current_module_name = uu____14973
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____14977 = FStar_ST.read last_env in
    match uu____14977 with
    | [] -> failwith "Empty env stack"
    | uu____14982::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____14990  ->
    let uu____14991 = FStar_ST.read last_env in
    match uu____14991 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___159_15002 = hd1 in
          {
            bindings = (uu___159_15002.bindings);
            depth = (uu___159_15002.depth);
            tcenv = (uu___159_15002.tcenv);
            warn = (uu___159_15002.warn);
            cache = refs;
            nolabels = (uu___159_15002.nolabels);
            use_zfuel_name = (uu___159_15002.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___159_15002.encode_non_total_function_typ);
            current_module_name = (uu___159_15002.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15008  ->
    let uu____15009 = FStar_ST.read last_env in
    match uu____15009 with
    | [] -> failwith "Popping an empty stack"
    | uu____15014::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15022  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15025  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15028  ->
    let uu____15029 = FStar_ST.read last_env in
    match uu____15029 with
    | hd1::uu____15035::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15041 -> failwith "Impossible"
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
        | (uu____15090::uu____15091,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___160_15095 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___160_15095.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___160_15095.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___160_15095.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15096 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15107 =
        let uu____15109 =
          let uu____15110 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15110 in
        let uu____15111 = open_fact_db_tags env in uu____15109 :: uu____15111 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15107
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
      let uu____15126 = encode_sigelt env se in
      match uu____15126 with
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
        let uu____15151 = FStar_Options.log_queries () in
        if uu____15151
        then
          let uu____15153 =
            let uu____15154 =
              let uu____15155 =
                let uu____15156 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15156 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15155 in
            FStar_SMTEncoding_Term.Caption uu____15154 in
          uu____15153 :: decls
        else decls in
      let env =
        let uu____15163 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15163 tcenv in
      let uu____15164 = encode_top_level_facts env se in
      match uu____15164 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15173 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15173))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15184 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15184
       then
         let uu____15185 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15185
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15206  ->
                 fun se  ->
                   match uu____15206 with
                   | (g,env2) ->
                       let uu____15218 = encode_top_level_facts env2 se in
                       (match uu____15218 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15231 =
         encode_signature
           (let uu___161_15235 = env in
            {
              bindings = (uu___161_15235.bindings);
              depth = (uu___161_15235.depth);
              tcenv = (uu___161_15235.tcenv);
              warn = false;
              cache = (uu___161_15235.cache);
              nolabels = (uu___161_15235.nolabels);
              use_zfuel_name = (uu___161_15235.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___161_15235.encode_non_total_function_typ);
              current_module_name = (uu___161_15235.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15231 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15247 = FStar_Options.log_queries () in
             if uu____15247
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___162_15252 = env1 in
               {
                 bindings = (uu___162_15252.bindings);
                 depth = (uu___162_15252.depth);
                 tcenv = (uu___162_15252.tcenv);
                 warn = true;
                 cache = (uu___162_15252.cache);
                 nolabels = (uu___162_15252.nolabels);
                 use_zfuel_name = (uu___162_15252.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___162_15252.encode_non_total_function_typ);
                 current_module_name = (uu___162_15252.current_module_name)
               });
            (let uu____15254 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15254
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
        (let uu____15289 =
           let uu____15290 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15290.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15289);
        (let env =
           let uu____15292 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15292 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15299 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15320 = aux rest in
                 (match uu____15320 with
                  | (out,rest1) ->
                      let t =
                        let uu____15338 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15338 with
                        | Some uu____15342 ->
                            let uu____15343 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15343
                              x.FStar_Syntax_Syntax.sort
                        | uu____15344 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15347 =
                        let uu____15349 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___163_15350 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___163_15350.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___163_15350.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15349 :: out in
                      (uu____15347, rest1))
             | uu____15353 -> ([], bindings1) in
           let uu____15357 = aux bindings in
           match uu____15357 with
           | (closing,bindings1) ->
               let uu____15371 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15371, bindings1) in
         match uu____15299 with
         | (q1,bindings1) ->
             let uu____15384 =
               let uu____15387 =
                 FStar_List.filter
                   (fun uu___129_15389  ->
                      match uu___129_15389 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15390 ->
                          false
                      | uu____15394 -> true) bindings1 in
               encode_env_bindings env uu____15387 in
             (match uu____15384 with
              | (env_decls,env1) ->
                  ((let uu____15405 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15405
                    then
                      let uu____15406 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15406
                    else ());
                   (let uu____15408 = encode_formula q1 env1 in
                    match uu____15408 with
                    | (phi,qdecls) ->
                        let uu____15420 =
                          let uu____15423 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15423 phi in
                        (match uu____15420 with
                         | (labels,phi1) ->
                             let uu____15433 = encode_labels labels in
                             (match uu____15433 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15454 =
                                      let uu____15458 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15459 =
                                        varops.mk_unique "@query" in
                                      (uu____15458, (Some "query"),
                                        uu____15459) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15454 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15472 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15472 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15474 = encode_formula q env in
       match uu____15474 with
       | (f,uu____15478) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15480) -> true
             | uu____15483 -> false)))