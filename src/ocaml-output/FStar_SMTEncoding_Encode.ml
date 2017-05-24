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
                         mk_term_projector_name lid (fst b)))
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
      FStar_All.pipe_left FStar_Pervasives.fst uu____498 in
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
          FStar_All.pipe_left FStar_Pervasives.snd uu____596 in
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
  FStar_SMTEncoding_Term.term option* FStar_SMTEncoding_Term.term option)
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
    (FStar_Ident.lident* Prims.string* FStar_SMTEncoding_Term.term option*
      FStar_SMTEncoding_Term.term option)
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
let caption_t: env_t -> FStar_Syntax_Syntax.term -> Prims.string option =
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
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option) option
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
      (Prims.string* FStar_SMTEncoding_Term.term option*
        FStar_SMTEncoding_Term.term option)
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
      Prims.string -> FStar_SMTEncoding_Term.term option -> env_t
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
  env_t -> FStar_Ident.lident -> FStar_SMTEncoding_Term.term option =
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
                             FStar_All.pipe_right uu____1407
                               FStar_Pervasives.fst in
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
let tok_of_name: env_t -> Prims.string -> FStar_SMTEncoding_Term.term option
  =
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
                match snd var with
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
      FStar_SMTEncoding_Term.term -> FStar_SMTEncoding_Term.term option
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
  FStar_SMTEncoding_Term.term option ->
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
                           let x = unmangle (fst b) in
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
  FStar_SMTEncoding_Term.term option ->
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
  FStar_SMTEncoding_Term.term option ->
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
                                                    x <> (fst fsym))) in
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
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
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
                        let uu____3182 = FStar_List.hd b in fst uu____3182 in
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
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
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
                                    FStar_All.pipe_right uu____3888
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____3885
                                    FStar_Pervasives.snd in
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
                        FStar_All.pipe_right uu____4219 FStar_Pervasives.fst in
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
                                                         FStar_Pervasives.snd
                                                         cvars1 in
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
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
                FStar_Syntax_Syntax.null_bv uu____4644 in
              gen_term_var env uu____4643 in
            match uu____4639 with
            | (scrsym,scr',env1) ->
                let uu____4654 = encode_term e env1 in
                (match uu____4654 with
                 | (scr,decls) ->
                     let uu____4661 =
                       let encode_branch b uu____4677 =
                         match uu____4677 with
                         | (else_case,decls1) ->
                             let uu____4688 =
                               FStar_Syntax_Subst.open_branch b in
                             (match uu____4688 with
                              | (p,w,br) ->
                                  let patterns = encode_pat env1 p in
                                  FStar_List.fold_right
                                    (fun uu____4718  ->
                                       fun uu____4719  ->
                                         match (uu____4718, uu____4719) with
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
                                                       fun uu____4756  ->
                                                         match uu____4756
                                                         with
                                                         | (x,t) ->
                                                             push_term_var
                                                               env2 x t) env1) in
                                             let uu____4761 =
                                               match w with
                                               | None  -> (guard, [])
                                               | Some w1 ->
                                                   let uu____4776 =
                                                     encode_term w1 env2 in
                                                   (match uu____4776 with
                                                    | (w2,decls21) ->
                                                        let uu____4784 =
                                                          let uu____4785 =
                                                            let uu____4788 =
                                                              let uu____4789
                                                                =
                                                                let uu____4792
                                                                  =
                                                                  FStar_SMTEncoding_Term.boxBool
                                                                    FStar_SMTEncoding_Util.mkTrue in
                                                                (w2,
                                                                  uu____4792) in
                                                              FStar_SMTEncoding_Util.mkEq
                                                                uu____4789 in
                                                            (guard,
                                                              uu____4788) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____4785 in
                                                        (uu____4784, decls21)) in
                                             (match uu____4761 with
                                              | (guard1,decls21) ->
                                                  let uu____4800 =
                                                    encode_br br env2 in
                                                  (match uu____4800 with
                                                   | (br1,decls3) ->
                                                       let uu____4808 =
                                                         FStar_SMTEncoding_Util.mkITE
                                                           (guard1, br1,
                                                             else_case1) in
                                                       (uu____4808,
                                                         (FStar_List.append
                                                            decls2
                                                            (FStar_List.append
                                                               decls21 decls3))))))
                                    patterns (else_case, decls1)) in
                       FStar_List.fold_right encode_branch pats
                         (default_case, decls) in
                     (match uu____4661 with
                      | (match_tm,decls1) ->
                          let uu____4820 =
                            FStar_SMTEncoding_Term.mkLet'
                              ([((scrsym, FStar_SMTEncoding_Term.Term_sort),
                                  scr)], match_tm) FStar_Range.dummyRange in
                          (uu____4820, decls1)))
and encode_pat:
  env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) Prims.list =
  fun env  ->
    fun pat  ->
      match pat.FStar_Syntax_Syntax.v with
      | FStar_Syntax_Syntax.Pat_disj ps ->
          FStar_List.map (encode_one_pat env) ps
      | uu____4851 -> let uu____4852 = encode_one_pat env pat in [uu____4852]
and encode_one_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
  fun env  ->
    fun pat  ->
      (let uu____4864 =
         FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
       if uu____4864
       then
         let uu____4865 = FStar_Syntax_Print.pat_to_string pat in
         FStar_Util.print1 "Encoding pattern %s\n" uu____4865
       else ());
      (let uu____4867 = FStar_TypeChecker_Util.decorated_pattern_as_term pat in
       match uu____4867 with
       | (vars,pat_term) ->
           let uu____4877 =
             FStar_All.pipe_right vars
               (FStar_List.fold_left
                  (fun uu____4900  ->
                     fun v1  ->
                       match uu____4900 with
                       | (env1,vars1) ->
                           let uu____4928 = gen_term_var env1 v1 in
                           (match uu____4928 with
                            | (xx,uu____4940,env2) ->
                                (env2,
                                  ((v1,
                                     (xx, FStar_SMTEncoding_Term.Term_sort))
                                  :: vars1)))) (env, [])) in
           (match uu____4877 with
            | (env1,vars1) ->
                let rec mk_guard pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____4987 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_var _
                    |FStar_Syntax_Syntax.Pat_wild _
                     |FStar_Syntax_Syntax.Pat_dot_term _ ->
                      FStar_SMTEncoding_Util.mkTrue
                  | FStar_Syntax_Syntax.Pat_constant c ->
                      let uu____4995 =
                        let uu____4998 = encode_const c in
                        (scrutinee, uu____4998) in
                      FStar_SMTEncoding_Util.mkEq uu____4995
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let is_f =
                        let tc_name =
                          FStar_TypeChecker_Env.typ_of_datacon env1.tcenv
                            (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                        let uu____5017 =
                          FStar_TypeChecker_Env.datacons_of_typ env1.tcenv
                            tc_name in
                        match uu____5017 with
                        | (uu____5021,uu____5022::[]) ->
                            FStar_SMTEncoding_Util.mkTrue
                        | uu____5024 ->
                            mk_data_tester env1
                              (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                              scrutinee in
                      let sub_term_guards =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5045  ->
                                  match uu____5045 with
                                  | (arg,uu____5051) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5061 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_guard arg uu____5061)) in
                      FStar_SMTEncoding_Util.mk_and_l (is_f ::
                        sub_term_guards) in
                let rec mk_projections pat1 scrutinee =
                  match pat1.FStar_Syntax_Syntax.v with
                  | FStar_Syntax_Syntax.Pat_disj uu____5080 ->
                      failwith "Impossible"
                  | FStar_Syntax_Syntax.Pat_dot_term (x,_)
                    |FStar_Syntax_Syntax.Pat_var x
                     |FStar_Syntax_Syntax.Pat_wild x -> [(x, scrutinee)]
                  | FStar_Syntax_Syntax.Pat_constant uu____5095 -> []
                  | FStar_Syntax_Syntax.Pat_cons (f,args) ->
                      let uu____5110 =
                        FStar_All.pipe_right args
                          (FStar_List.mapi
                             (fun i  ->
                                fun uu____5132  ->
                                  match uu____5132 with
                                  | (arg,uu____5141) ->
                                      let proj =
                                        primitive_projector_by_pos env1.tcenv
                                          (f.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v
                                          i in
                                      let uu____5151 =
                                        FStar_SMTEncoding_Util.mkApp
                                          (proj, [scrutinee]) in
                                      mk_projections arg uu____5151)) in
                      FStar_All.pipe_right uu____5110 FStar_List.flatten in
                let pat_term1 uu____5167 = encode_term pat_term env1 in
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
      let uu____5174 =
        FStar_All.pipe_right l
          (FStar_List.fold_left
             (fun uu____5189  ->
                fun uu____5190  ->
                  match (uu____5189, uu____5190) with
                  | ((tms,decls),(t,uu____5210)) ->
                      let uu____5221 = encode_term t env in
                      (match uu____5221 with
                       | (t1,decls') ->
                           ((t1 :: tms), (FStar_List.append decls decls'))))
             ([], [])) in
      match uu____5174 with | (l1,decls) -> ((FStar_List.rev l1), decls)
and encode_function_type_as_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5255 = FStar_Syntax_Util.list_elements e in
        match uu____5255 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5273 =
          let uu____5283 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5283 FStar_Syntax_Util.head_and_args in
        match uu____5273 with
        | (head1,args) ->
            let uu____5314 =
              let uu____5322 =
                let uu____5323 = FStar_Syntax_Util.un_uinst head1 in
                uu____5323.FStar_Syntax_Syntax.n in
              (uu____5322, args) in
            (match uu____5314 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5337,uu____5338)::(e,uu____5340)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5371)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5392 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5425 =
            let uu____5435 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5435 FStar_Syntax_Util.head_and_args in
          match uu____5425 with
          | (head1,args) ->
              let uu____5464 =
                let uu____5472 =
                  let uu____5473 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5473.FStar_Syntax_Syntax.n in
                (uu____5472, args) in
              (match uu____5464 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5486)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5506 -> None) in
        match elts with
        | t1::[] ->
            let uu____5524 = smt_pat_or t1 in
            (match uu____5524 with
             | Some e ->
                 let uu____5540 = list_elements1 e in
                 FStar_All.pipe_right uu____5540
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5557 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5557
                           (FStar_List.map one_pat)))
             | uu____5571 ->
                 let uu____5575 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5575])
        | uu____5606 ->
            let uu____5608 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5608] in
      let uu____5639 =
        let uu____5655 =
          let uu____5656 = FStar_Syntax_Subst.compress t in
          uu____5656.FStar_Syntax_Syntax.n in
        match uu____5655 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5686 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5686 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5721;
                        FStar_Syntax_Syntax.effect_name = uu____5722;
                        FStar_Syntax_Syntax.result_typ = uu____5723;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5725)::(post,uu____5727)::(pats,uu____5729)::[];
                        FStar_Syntax_Syntax.flags = uu____5730;_}
                      ->
                      let uu____5762 = lemma_pats pats in
                      (binders1, pre, post, uu____5762)
                  | uu____5781 -> failwith "impos"))
        | uu____5797 -> failwith "Impos" in
      match uu____5639 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5842 = env in
            {
              bindings = (uu___137_5842.bindings);
              depth = (uu___137_5842.depth);
              tcenv = (uu___137_5842.tcenv);
              warn = (uu___137_5842.warn);
              cache = (uu___137_5842.cache);
              nolabels = (uu___137_5842.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5842.encode_non_total_function_typ);
              current_module_name = (uu___137_5842.current_module_name)
            } in
          let uu____5843 = encode_binders None binders env1 in
          (match uu____5843 with
           | (vars,guards,env2,decls,uu____5858) ->
               let uu____5865 =
                 let uu____5872 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____5903 =
                             let uu____5908 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____5924  ->
                                       match uu____5924 with
                                       | (t1,uu____5931) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____5908 FStar_List.unzip in
                           match uu____5903 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5872 FStar_List.unzip in
               (match uu____5865 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_5981 = env2 in
                      {
                        bindings = (uu___138_5981.bindings);
                        depth = (uu___138_5981.depth);
                        tcenv = (uu___138_5981.tcenv);
                        warn = (uu___138_5981.warn);
                        cache = (uu___138_5981.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_5981.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_5981.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_5981.current_module_name)
                      } in
                    let uu____5982 =
                      let uu____5985 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____5985 env3 in
                    (match uu____5982 with
                     | (pre1,decls'') ->
                         let uu____5990 =
                           let uu____5993 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____5993 env3 in
                         (match uu____5990 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6000 =
                                let uu____6001 =
                                  let uu____6007 =
                                    let uu____6008 =
                                      let uu____6011 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6011, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6008 in
                                  (pats, vars, uu____6007) in
                                FStar_SMTEncoding_Util.mkForall uu____6001 in
                              (uu____6000, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6024 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6024
        then
          let uu____6025 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6026 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6025 uu____6026
        else () in
      let enc f r l =
        let uu____6053 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6066 = encode_term (fst x) env in
                 match uu____6066 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6053 with
        | (decls,args) ->
            let uu____6083 =
              let uu___139_6084 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6084.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6084.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6083, decls) in
      let const_op f r uu____6103 = let uu____6106 = f r in (uu____6106, []) in
      let un_op f l =
        let uu____6122 = FStar_List.hd l in FStar_All.pipe_left f uu____6122 in
      let bin_op f uu___111_6135 =
        match uu___111_6135 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6143 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6170 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6179  ->
                 match uu____6179 with
                 | (t,uu____6187) ->
                     let uu____6188 = encode_formula t env in
                     (match uu____6188 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6170 with
        | (decls,phis) ->
            let uu____6205 =
              let uu___140_6206 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6206.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6206.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6205, decls) in
      let eq_op r uu___112_6222 =
        match uu___112_6222 with
        | _::e1::e2::[]|_::_::e1::e2::[] ->
            let uu____6282 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6282 r [e1; e2]
        | l ->
            let uu____6302 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6302 r l in
      let mk_imp1 r uu___113_6321 =
        match uu___113_6321 with
        | (lhs,uu____6325)::(rhs,uu____6327)::[] ->
            let uu____6348 = encode_formula rhs env in
            (match uu____6348 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6357) ->
                      (l1, decls1)
                  | uu____6360 ->
                      let uu____6361 = encode_formula lhs env in
                      (match uu____6361 with
                       | (l2,decls2) ->
                           let uu____6368 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6368, (FStar_List.append decls1 decls2)))))
        | uu____6370 -> failwith "impossible" in
      let mk_ite r uu___114_6385 =
        match uu___114_6385 with
        | (guard,uu____6389)::(_then,uu____6391)::(_else,uu____6393)::[] ->
            let uu____6422 = encode_formula guard env in
            (match uu____6422 with
             | (g,decls1) ->
                 let uu____6429 = encode_formula _then env in
                 (match uu____6429 with
                  | (t,decls2) ->
                      let uu____6436 = encode_formula _else env in
                      (match uu____6436 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6445 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6464 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6464 in
      let connectives =
        let uu____6476 =
          let uu____6485 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6485) in
        let uu____6498 =
          let uu____6508 =
            let uu____6517 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6517) in
          let uu____6530 =
            let uu____6540 =
              let uu____6550 =
                let uu____6559 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6559) in
              let uu____6572 =
                let uu____6582 =
                  let uu____6592 =
                    let uu____6601 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6601) in
                  [uu____6592;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6582 in
              uu____6550 :: uu____6572 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6540 in
          uu____6508 :: uu____6530 in
        uu____6476 :: uu____6498 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6763 = encode_formula phi' env in
            (match uu____6763 with
             | (phi2,decls) ->
                 let uu____6770 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6770, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6771 ->
            let uu____6776 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6776 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6805 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6805 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6813;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6815;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6831 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6831 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6863::(x,uu____6865)::(t,uu____6867)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____6901 = encode_term x env in
                 (match uu____6901 with
                  | (x1,decls) ->
                      let uu____6908 = encode_term t env in
                      (match uu____6908 with
                       | (t1,decls') ->
                           let uu____6915 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____6915, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____6919)::(msg,uu____6921)::(phi2,uu____6923)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____6957 =
                   let uu____6960 =
                     let uu____6961 = FStar_Syntax_Subst.compress r in
                     uu____6961.FStar_Syntax_Syntax.n in
                   let uu____6964 =
                     let uu____6965 = FStar_Syntax_Subst.compress msg in
                     uu____6965.FStar_Syntax_Syntax.n in
                   (uu____6960, uu____6964) in
                 (match uu____6957 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____6972))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____6988 -> fallback phi2)
             | uu____6991 when head_redex env head2 ->
                 let uu____6999 = whnf env phi1 in
                 encode_formula uu____6999 env
             | uu____7000 ->
                 let uu____7008 = encode_term phi1 env in
                 (match uu____7008 with
                  | (tt,decls) ->
                      let uu____7015 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7016 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7016.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7016.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7015, decls)))
        | uu____7019 ->
            let uu____7020 = encode_term phi1 env in
            (match uu____7020 with
             | (tt,decls) ->
                 let uu____7027 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7028 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7028.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7028.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7027, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7055 = encode_binders None bs env1 in
        match uu____7055 with
        | (vars,guards,env2,decls,uu____7077) ->
            let uu____7084 =
              let uu____7091 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7114 =
                          let uu____7119 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7133  ->
                                    match uu____7133 with
                                    | (t,uu____7139) ->
                                        encode_term t
                                          (let uu___143_7140 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7140.bindings);
                                             depth = (uu___143_7140.depth);
                                             tcenv = (uu___143_7140.tcenv);
                                             warn = (uu___143_7140.warn);
                                             cache = (uu___143_7140.cache);
                                             nolabels =
                                               (uu___143_7140.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7140.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7140.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7119 FStar_List.unzip in
                        match uu____7114 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7091 FStar_List.unzip in
            (match uu____7084 with
             | (pats,decls') ->
                 let uu____7192 = encode_formula body env2 in
                 (match uu____7192 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7211;
                             FStar_SMTEncoding_Term.rng = uu____7212;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7220 -> guards in
                      let uu____7223 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7223, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7257  ->
                   match uu____7257 with
                   | (x,uu____7261) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7267 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7273 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7273) uu____7267 tl1 in
             let uu____7275 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7287  ->
                       match uu____7287 with
                       | (b,uu____7291) ->
                           let uu____7292 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7292)) in
             (match uu____7275 with
              | None  -> ()
              | Some (x,uu____7296) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7306 =
                    let uu____7307 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7307 in
                  FStar_Errors.warn pos uu____7306) in
       let uu____7308 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7308 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7314 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7350  ->
                     match uu____7350 with
                     | (l,uu____7360) -> FStar_Ident.lid_equals op l)) in
           (match uu____7314 with
            | None  -> fallback phi1
            | Some (uu____7383,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7412 = encode_q_body env vars pats body in
             match uu____7412 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7438 =
                     let uu____7444 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7444) in
                   FStar_SMTEncoding_Term.mkForall uu____7438
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7456 = encode_q_body env vars pats body in
             match uu____7456 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7481 =
                   let uu____7482 =
                     let uu____7488 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7488) in
                   FStar_SMTEncoding_Term.mkExists uu____7482
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7481, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7537 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7537 with
  | (asym,a) ->
      let uu____7542 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7542 with
       | (xsym,x) ->
           let uu____7547 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7547 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7577 =
                      let uu____7583 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7583, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7577 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7598 =
                      let uu____7602 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7602) in
                    FStar_SMTEncoding_Util.mkApp uu____7598 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7610 =
                    let uu____7612 =
                      let uu____7614 =
                        let uu____7616 =
                          let uu____7617 =
                            let uu____7621 =
                              let uu____7622 =
                                let uu____7628 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7628) in
                              FStar_SMTEncoding_Util.mkForall uu____7622 in
                            (uu____7621, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7617 in
                        let uu____7637 =
                          let uu____7639 =
                            let uu____7640 =
                              let uu____7644 =
                                let uu____7645 =
                                  let uu____7651 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7651) in
                                FStar_SMTEncoding_Util.mkForall uu____7645 in
                              (uu____7644,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7640 in
                          [uu____7639] in
                        uu____7616 :: uu____7637 in
                      xtok_decl :: uu____7614 in
                    xname_decl :: uu____7612 in
                  (xtok1, uu____7610) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7700 =
                    let uu____7708 =
                      let uu____7714 =
                        let uu____7715 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7715 in
                      quant axy uu____7714 in
                    (FStar_Syntax_Const.op_Eq, uu____7708) in
                  let uu____7721 =
                    let uu____7730 =
                      let uu____7738 =
                        let uu____7744 =
                          let uu____7745 =
                            let uu____7746 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7746 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7745 in
                        quant axy uu____7744 in
                      (FStar_Syntax_Const.op_notEq, uu____7738) in
                    let uu____7752 =
                      let uu____7761 =
                        let uu____7769 =
                          let uu____7775 =
                            let uu____7776 =
                              let uu____7777 =
                                let uu____7780 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7781 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7780, uu____7781) in
                              FStar_SMTEncoding_Util.mkLT uu____7777 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7776 in
                          quant xy uu____7775 in
                        (FStar_Syntax_Const.op_LT, uu____7769) in
                      let uu____7787 =
                        let uu____7796 =
                          let uu____7804 =
                            let uu____7810 =
                              let uu____7811 =
                                let uu____7812 =
                                  let uu____7815 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7816 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7815, uu____7816) in
                                FStar_SMTEncoding_Util.mkLTE uu____7812 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7811 in
                            quant xy uu____7810 in
                          (FStar_Syntax_Const.op_LTE, uu____7804) in
                        let uu____7822 =
                          let uu____7831 =
                            let uu____7839 =
                              let uu____7845 =
                                let uu____7846 =
                                  let uu____7847 =
                                    let uu____7850 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7851 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7850, uu____7851) in
                                  FStar_SMTEncoding_Util.mkGT uu____7847 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7846 in
                              quant xy uu____7845 in
                            (FStar_Syntax_Const.op_GT, uu____7839) in
                          let uu____7857 =
                            let uu____7866 =
                              let uu____7874 =
                                let uu____7880 =
                                  let uu____7881 =
                                    let uu____7882 =
                                      let uu____7885 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____7886 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____7885, uu____7886) in
                                    FStar_SMTEncoding_Util.mkGTE uu____7882 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____7881 in
                                quant xy uu____7880 in
                              (FStar_Syntax_Const.op_GTE, uu____7874) in
                            let uu____7892 =
                              let uu____7901 =
                                let uu____7909 =
                                  let uu____7915 =
                                    let uu____7916 =
                                      let uu____7917 =
                                        let uu____7920 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____7921 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____7920, uu____7921) in
                                      FStar_SMTEncoding_Util.mkSub uu____7917 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____7916 in
                                  quant xy uu____7915 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____7909) in
                              let uu____7927 =
                                let uu____7936 =
                                  let uu____7944 =
                                    let uu____7950 =
                                      let uu____7951 =
                                        let uu____7952 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____7952 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____7951 in
                                    quant qx uu____7950 in
                                  (FStar_Syntax_Const.op_Minus, uu____7944) in
                                let uu____7958 =
                                  let uu____7967 =
                                    let uu____7975 =
                                      let uu____7981 =
                                        let uu____7982 =
                                          let uu____7983 =
                                            let uu____7986 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____7987 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____7986, uu____7987) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____7983 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____7982 in
                                      quant xy uu____7981 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____7975) in
                                  let uu____7993 =
                                    let uu____8002 =
                                      let uu____8010 =
                                        let uu____8016 =
                                          let uu____8017 =
                                            let uu____8018 =
                                              let uu____8021 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8022 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8021, uu____8022) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8018 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8017 in
                                        quant xy uu____8016 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8010) in
                                    let uu____8028 =
                                      let uu____8037 =
                                        let uu____8045 =
                                          let uu____8051 =
                                            let uu____8052 =
                                              let uu____8053 =
                                                let uu____8056 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8057 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8056, uu____8057) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8053 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8052 in
                                          quant xy uu____8051 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8045) in
                                      let uu____8063 =
                                        let uu____8072 =
                                          let uu____8080 =
                                            let uu____8086 =
                                              let uu____8087 =
                                                let uu____8088 =
                                                  let uu____8091 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8092 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8091, uu____8092) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8088 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8087 in
                                            quant xy uu____8086 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8080) in
                                        let uu____8098 =
                                          let uu____8107 =
                                            let uu____8115 =
                                              let uu____8121 =
                                                let uu____8122 =
                                                  let uu____8123 =
                                                    let uu____8126 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8127 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8126, uu____8127) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8123 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8122 in
                                              quant xy uu____8121 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8115) in
                                          let uu____8133 =
                                            let uu____8142 =
                                              let uu____8150 =
                                                let uu____8156 =
                                                  let uu____8157 =
                                                    let uu____8158 =
                                                      let uu____8161 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8162 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8161,
                                                        uu____8162) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8158 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8157 in
                                                quant xy uu____8156 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8150) in
                                            let uu____8168 =
                                              let uu____8177 =
                                                let uu____8185 =
                                                  let uu____8191 =
                                                    let uu____8192 =
                                                      let uu____8193 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8193 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8192 in
                                                  quant qx uu____8191 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8185) in
                                              [uu____8177] in
                                            uu____8142 :: uu____8168 in
                                          uu____8107 :: uu____8133 in
                                        uu____8072 :: uu____8098 in
                                      uu____8037 :: uu____8063 in
                                    uu____8002 :: uu____8028 in
                                  uu____7967 :: uu____7993 in
                                uu____7936 :: uu____7958 in
                              uu____7901 :: uu____7927 in
                            uu____7866 :: uu____7892 in
                          uu____7831 :: uu____7857 in
                        uu____7796 :: uu____7822 in
                      uu____7761 :: uu____7787 in
                    uu____7730 :: uu____7752 in
                  uu____7700 :: uu____7721 in
                let mk1 l v1 =
                  let uu____8321 =
                    let uu____8326 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8358  ->
                              match uu____8358 with
                              | (l',uu____8367) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8326
                      (FStar_Option.map
                         (fun uu____8400  ->
                            match uu____8400 with | (uu____8411,b) -> b v1)) in
                  FStar_All.pipe_right uu____8321 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8452  ->
                          match uu____8452 with
                          | (l',uu____8461) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8487 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8487 with
        | (xxsym,xx) ->
            let uu____8492 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8492 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8500 =
                   let uu____8504 =
                     let uu____8505 =
                       let uu____8511 =
                         let uu____8512 =
                           let uu____8515 =
                             let uu____8516 =
                               let uu____8519 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8519) in
                             FStar_SMTEncoding_Util.mkEq uu____8516 in
                           (xx_has_type, uu____8515) in
                         FStar_SMTEncoding_Util.mkImp uu____8512 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8511) in
                     FStar_SMTEncoding_Util.mkForall uu____8505 in
                   let uu____8532 =
                     let uu____8533 =
                       let uu____8534 =
                         let uu____8535 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8535 in
                       Prims.strcat module_name uu____8534 in
                     varops.mk_unique uu____8533 in
                   (uu____8504, (Some "pretyping"), uu____8532) in
                 FStar_SMTEncoding_Util.mkAssume uu____8500)
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
    let uu____8565 =
      let uu____8566 =
        let uu____8570 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8570, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8566 in
    let uu____8572 =
      let uu____8574 =
        let uu____8575 =
          let uu____8579 =
            let uu____8580 =
              let uu____8586 =
                let uu____8587 =
                  let uu____8590 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8590) in
                FStar_SMTEncoding_Util.mkImp uu____8587 in
              ([[typing_pred]], [xx], uu____8586) in
            mkForall_fuel uu____8580 in
          (uu____8579, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8575 in
      [uu____8574] in
    uu____8565 :: uu____8572 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8618 =
      let uu____8619 =
        let uu____8623 =
          let uu____8624 =
            let uu____8630 =
              let uu____8633 =
                let uu____8635 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8635] in
              [uu____8633] in
            let uu____8638 =
              let uu____8639 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8639 tt in
            (uu____8630, [bb], uu____8638) in
          FStar_SMTEncoding_Util.mkForall uu____8624 in
        (uu____8623, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8619 in
    let uu____8650 =
      let uu____8652 =
        let uu____8653 =
          let uu____8657 =
            let uu____8658 =
              let uu____8664 =
                let uu____8665 =
                  let uu____8668 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8668) in
                FStar_SMTEncoding_Util.mkImp uu____8665 in
              ([[typing_pred]], [xx], uu____8664) in
            mkForall_fuel uu____8658 in
          (uu____8657, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8653 in
      [uu____8652] in
    uu____8618 :: uu____8650 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8702 =
        let uu____8703 =
          let uu____8707 =
            let uu____8709 =
              let uu____8711 =
                let uu____8713 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8714 =
                  let uu____8716 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8716] in
                uu____8713 :: uu____8714 in
              tt :: uu____8711 in
            tt :: uu____8709 in
          ("Prims.Precedes", uu____8707) in
        FStar_SMTEncoding_Util.mkApp uu____8703 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8702 in
    let precedes_y_x =
      let uu____8719 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8719 in
    let uu____8721 =
      let uu____8722 =
        let uu____8726 =
          let uu____8727 =
            let uu____8733 =
              let uu____8736 =
                let uu____8738 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8738] in
              [uu____8736] in
            let uu____8741 =
              let uu____8742 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8742 tt in
            (uu____8733, [bb], uu____8741) in
          FStar_SMTEncoding_Util.mkForall uu____8727 in
        (uu____8726, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8722 in
    let uu____8753 =
      let uu____8755 =
        let uu____8756 =
          let uu____8760 =
            let uu____8761 =
              let uu____8767 =
                let uu____8768 =
                  let uu____8771 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8771) in
                FStar_SMTEncoding_Util.mkImp uu____8768 in
              ([[typing_pred]], [xx], uu____8767) in
            mkForall_fuel uu____8761 in
          (uu____8760, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8756 in
      let uu____8784 =
        let uu____8786 =
          let uu____8787 =
            let uu____8791 =
              let uu____8792 =
                let uu____8798 =
                  let uu____8799 =
                    let uu____8802 =
                      let uu____8803 =
                        let uu____8805 =
                          let uu____8807 =
                            let uu____8809 =
                              let uu____8810 =
                                let uu____8813 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8814 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8813, uu____8814) in
                              FStar_SMTEncoding_Util.mkGT uu____8810 in
                            let uu____8815 =
                              let uu____8817 =
                                let uu____8818 =
                                  let uu____8821 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8822 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8821, uu____8822) in
                                FStar_SMTEncoding_Util.mkGTE uu____8818 in
                              let uu____8823 =
                                let uu____8825 =
                                  let uu____8826 =
                                    let uu____8829 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8830 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8829, uu____8830) in
                                  FStar_SMTEncoding_Util.mkLT uu____8826 in
                                [uu____8825] in
                              uu____8817 :: uu____8823 in
                            uu____8809 :: uu____8815 in
                          typing_pred_y :: uu____8807 in
                        typing_pred :: uu____8805 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8803 in
                    (uu____8802, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8799 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8798) in
              mkForall_fuel uu____8792 in
            (uu____8791, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8787 in
        [uu____8786] in
      uu____8755 :: uu____8784 in
    uu____8721 :: uu____8753 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8860 =
      let uu____8861 =
        let uu____8865 =
          let uu____8866 =
            let uu____8872 =
              let uu____8875 =
                let uu____8877 = FStar_SMTEncoding_Term.boxString b in
                [uu____8877] in
              [uu____8875] in
            let uu____8880 =
              let uu____8881 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____8881 tt in
            (uu____8872, [bb], uu____8880) in
          FStar_SMTEncoding_Util.mkForall uu____8866 in
        (uu____8865, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8861 in
    let uu____8892 =
      let uu____8894 =
        let uu____8895 =
          let uu____8899 =
            let uu____8900 =
              let uu____8906 =
                let uu____8907 =
                  let uu____8910 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____8910) in
                FStar_SMTEncoding_Util.mkImp uu____8907 in
              ([[typing_pred]], [xx], uu____8906) in
            mkForall_fuel uu____8900 in
          (uu____8899, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8895 in
      [uu____8894] in
    uu____8860 :: uu____8892 in
  let mk_ref1 env reft_name uu____8932 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____8943 =
        let uu____8947 =
          let uu____8949 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____8949] in
        (reft_name, uu____8947) in
      FStar_SMTEncoding_Util.mkApp uu____8943 in
    let refb =
      let uu____8952 =
        let uu____8956 =
          let uu____8958 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____8958] in
        (reft_name, uu____8956) in
      FStar_SMTEncoding_Util.mkApp uu____8952 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____8962 =
      let uu____8963 =
        let uu____8967 =
          let uu____8968 =
            let uu____8974 =
              let uu____8975 =
                let uu____8978 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____8978) in
              FStar_SMTEncoding_Util.mkImp uu____8975 in
            ([[typing_pred]], [xx; aa], uu____8974) in
          mkForall_fuel uu____8968 in
        (uu____8967, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____8963 in
    [uu____8962] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9018 =
      let uu____9019 =
        let uu____9023 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9023, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9019 in
    [uu____9018] in
  let mk_and_interp env conj uu____9034 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9051 =
      let uu____9052 =
        let uu____9056 =
          let uu____9057 =
            let uu____9063 =
              let uu____9064 =
                let uu____9067 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9067, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9064 in
            ([[l_and_a_b]], [aa; bb], uu____9063) in
          FStar_SMTEncoding_Util.mkForall uu____9057 in
        (uu____9056, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9052 in
    [uu____9051] in
  let mk_or_interp env disj uu____9091 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9108 =
      let uu____9109 =
        let uu____9113 =
          let uu____9114 =
            let uu____9120 =
              let uu____9121 =
                let uu____9124 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9124, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9121 in
            ([[l_or_a_b]], [aa; bb], uu____9120) in
          FStar_SMTEncoding_Util.mkForall uu____9114 in
        (uu____9113, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9109 in
    [uu____9108] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9165 =
      let uu____9166 =
        let uu____9170 =
          let uu____9171 =
            let uu____9177 =
              let uu____9178 =
                let uu____9181 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9181, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9178 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9177) in
          FStar_SMTEncoding_Util.mkForall uu____9171 in
        (uu____9170, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9166 in
    [uu____9165] in
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
    let uu____9228 =
      let uu____9229 =
        let uu____9233 =
          let uu____9234 =
            let uu____9240 =
              let uu____9241 =
                let uu____9244 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9244, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9241 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9240) in
          FStar_SMTEncoding_Util.mkForall uu____9234 in
        (uu____9233, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9229 in
    [uu____9228] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9289 =
      let uu____9290 =
        let uu____9294 =
          let uu____9295 =
            let uu____9301 =
              let uu____9302 =
                let uu____9305 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9305, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9302 in
            ([[l_imp_a_b]], [aa; bb], uu____9301) in
          FStar_SMTEncoding_Util.mkForall uu____9295 in
        (uu____9294, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9290 in
    [uu____9289] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9346 =
      let uu____9347 =
        let uu____9351 =
          let uu____9352 =
            let uu____9358 =
              let uu____9359 =
                let uu____9362 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9362, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9359 in
            ([[l_iff_a_b]], [aa; bb], uu____9358) in
          FStar_SMTEncoding_Util.mkForall uu____9352 in
        (uu____9351, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9347 in
    [uu____9346] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9396 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9396 in
    let uu____9398 =
      let uu____9399 =
        let uu____9403 =
          let uu____9404 =
            let uu____9410 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9410) in
          FStar_SMTEncoding_Util.mkForall uu____9404 in
        (uu____9403, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9399 in
    [uu____9398] in
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
      let uu____9450 =
        let uu____9454 =
          let uu____9456 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9456] in
        ("Valid", uu____9454) in
      FStar_SMTEncoding_Util.mkApp uu____9450 in
    let uu____9458 =
      let uu____9459 =
        let uu____9463 =
          let uu____9464 =
            let uu____9470 =
              let uu____9471 =
                let uu____9474 =
                  let uu____9475 =
                    let uu____9481 =
                      let uu____9484 =
                        let uu____9486 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9486] in
                      [uu____9484] in
                    let uu____9489 =
                      let uu____9490 =
                        let uu____9493 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9493, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9490 in
                    (uu____9481, [xx1], uu____9489) in
                  FStar_SMTEncoding_Util.mkForall uu____9475 in
                (uu____9474, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9471 in
            ([[l_forall_a_b]], [aa; bb], uu____9470) in
          FStar_SMTEncoding_Util.mkForall uu____9464 in
        (uu____9463, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9459 in
    [uu____9458] in
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
      let uu____9544 =
        let uu____9548 =
          let uu____9550 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9550] in
        ("Valid", uu____9548) in
      FStar_SMTEncoding_Util.mkApp uu____9544 in
    let uu____9552 =
      let uu____9553 =
        let uu____9557 =
          let uu____9558 =
            let uu____9564 =
              let uu____9565 =
                let uu____9568 =
                  let uu____9569 =
                    let uu____9575 =
                      let uu____9578 =
                        let uu____9580 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9580] in
                      [uu____9578] in
                    let uu____9583 =
                      let uu____9584 =
                        let uu____9587 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9587, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9584 in
                    (uu____9575, [xx1], uu____9583) in
                  FStar_SMTEncoding_Util.mkExists uu____9569 in
                (uu____9568, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9565 in
            ([[l_exists_a_b]], [aa; bb], uu____9564) in
          FStar_SMTEncoding_Util.mkForall uu____9558 in
        (uu____9557, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9553 in
    [uu____9552] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9623 =
      let uu____9624 =
        let uu____9628 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9629 = varops.mk_unique "typing_range_const" in
        (uu____9628, (Some "Range_const typing"), uu____9629) in
      FStar_SMTEncoding_Util.mkAssume uu____9624 in
    [uu____9623] in
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
          let uu____9891 =
            FStar_Util.find_opt
              (fun uu____9909  ->
                 match uu____9909 with
                 | (l,uu____9919) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____9891 with
          | None  -> []
          | Some (uu____9941,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____9978 = encode_function_type_as_formula t env in
        match uu____9978 with
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
            let uu____10010 =
              (let uu____10011 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10011) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10010
            then
              let uu____10015 = new_term_constant_and_tok_from_lid env lid in
              match uu____10015 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10027 =
                      let uu____10028 = FStar_Syntax_Subst.compress t_norm in
                      uu____10028.FStar_Syntax_Syntax.n in
                    match uu____10027 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10033) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10050  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10053 -> [] in
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
              (let uu____10062 = prims.is lid in
               if uu____10062
               then
                 let vname = varops.new_fvar lid in
                 let uu____10067 = prims.mk lid vname in
                 match uu____10067 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10082 =
                    let uu____10088 = curried_arrow_formals_comp t_norm in
                    match uu____10088 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10099 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10099
                          then
                            let uu____10100 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10101 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10101.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10101.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10101.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10101.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10101.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10101.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10101.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10101.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10101.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10101.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10101.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10101.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10101.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10101.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10101.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10101.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10101.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10101.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10101.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10101.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10101.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10101.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10101.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10100
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10108 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10108)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10082 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10135 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10135 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10148 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10172  ->
                                     match uu___115_10172 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10175 =
                                           FStar_Util.prefix vars in
                                         (match uu____10175 with
                                          | (uu____10186,(xxsym,uu____10188))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10198 =
                                                let uu____10199 =
                                                  let uu____10203 =
                                                    let uu____10204 =
                                                      let uu____10210 =
                                                        let uu____10211 =
                                                          let uu____10214 =
                                                            let uu____10215 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10215 in
                                                          (vapp, uu____10214) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10211 in
                                                      ([[vapp]], vars,
                                                        uu____10210) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10204 in
                                                  (uu____10203,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10199 in
                                              [uu____10198])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10226 =
                                           FStar_Util.prefix vars in
                                         (match uu____10226 with
                                          | (uu____10237,(xxsym,uu____10239))
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
                                              let uu____10253 =
                                                let uu____10254 =
                                                  let uu____10258 =
                                                    let uu____10259 =
                                                      let uu____10265 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10265) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10259 in
                                                  (uu____10258,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10254 in
                                              [uu____10253])
                                     | uu____10274 -> [])) in
                           let uu____10275 = encode_binders None formals env1 in
                           (match uu____10275 with
                            | (vars,guards,env',decls1,uu____10291) ->
                                let uu____10298 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10303 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10303, decls1)
                                  | Some p ->
                                      let uu____10305 = encode_formula p env' in
                                      (match uu____10305 with
                                       | (g,ds) ->
                                           let uu____10312 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10312,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10298 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10321 =
                                         let uu____10325 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10325) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10321 in
                                     let uu____10330 =
                                       let vname_decl =
                                         let uu____10335 =
                                           let uu____10341 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10346  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10341,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10335 in
                                       let uu____10351 =
                                         let env2 =
                                           let uu___145_10355 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10355.bindings);
                                             depth = (uu___145_10355.depth);
                                             tcenv = (uu___145_10355.tcenv);
                                             warn = (uu___145_10355.warn);
                                             cache = (uu___145_10355.cache);
                                             nolabels =
                                               (uu___145_10355.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10355.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10355.current_module_name)
                                           } in
                                         let uu____10356 =
                                           let uu____10357 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10357 in
                                         if uu____10356
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10351 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10367::uu____10368 ->
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
                                                   let uu____10391 =
                                                     let uu____10397 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10397) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10391 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10411 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10413 =
                                             match formals with
                                             | [] ->
                                                 let uu____10422 =
                                                   let uu____10423 =
                                                     let uu____10425 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10425 in
                                                   push_free_var env1 lid
                                                     vname uu____10423 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10422)
                                             | uu____10428 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10433 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10433 in
                                                 let name_tok_corr =
                                                   let uu____10435 =
                                                     let uu____10439 =
                                                       let uu____10440 =
                                                         let uu____10446 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10446) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10440 in
                                                     (uu____10439,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10435 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10413 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10330 with
                                      | (decls2,env2) ->
                                          let uu____10470 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10475 =
                                              encode_term res_t1 env' in
                                            match uu____10475 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10483 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10483,
                                                  decls) in
                                          (match uu____10470 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10491 =
                                                   let uu____10495 =
                                                     let uu____10496 =
                                                       let uu____10502 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10502) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10496 in
                                                   (uu____10495,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10491 in
                                               let freshness =
                                                 let uu____10511 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10511
                                                 then
                                                   let uu____10514 =
                                                     let uu____10515 =
                                                       let uu____10521 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10527 =
                                                         varops.next_id () in
                                                       (vname, uu____10521,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10527) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10515 in
                                                   let uu____10529 =
                                                     let uu____10531 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10531] in
                                                   uu____10514 :: uu____10529
                                                 else [] in
                                               let g =
                                                 let uu____10535 =
                                                   let uu____10537 =
                                                     let uu____10539 =
                                                       let uu____10541 =
                                                         let uu____10543 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10543 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10541 in
                                                     FStar_List.append decls3
                                                       uu____10539 in
                                                   FStar_List.append decls2
                                                     uu____10537 in
                                                 FStar_List.append decls11
                                                   uu____10535 in
                                               (g, env2))))))))
let declare_top_level_let:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.term ->
        FStar_Syntax_Syntax.term ->
          ((Prims.string* FStar_SMTEncoding_Term.term option)*
            FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun x  ->
      fun t  ->
        fun t_norm  ->
          let uu____10565 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10565 with
          | None  ->
              let uu____10588 = encode_free_var env x t t_norm [] in
              (match uu____10588 with
               | (decls,env1) ->
                   let uu____10603 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10603 with
                    | (n1,x',uu____10622) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10634) -> ((n1, x1), [], env)
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
          let uu____10667 = encode_free_var env lid t tt quals in
          match uu____10667 with
          | (decls,env1) ->
              let uu____10678 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10678
              then
                let uu____10682 =
                  let uu____10684 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10684 in
                (uu____10682, env1)
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
             (fun uu____10712  ->
                fun lb  ->
                  match uu____10712 with
                  | (decls,env1) ->
                      let uu____10724 =
                        let uu____10728 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10728
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10724 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10742 = FStar_Syntax_Util.head_and_args t in
    match uu____10742 with
    | (hd1,args) ->
        let uu____10768 =
          let uu____10769 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10769.FStar_Syntax_Syntax.n in
        (match uu____10768 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10773,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10786 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10801  ->
      fun quals  ->
        match uu____10801 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10850 = FStar_Util.first_N nbinders formals in
              match uu____10850 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____10890  ->
                         fun uu____10891  ->
                           match (uu____10890, uu____10891) with
                           | ((formal,uu____10901),(binder,uu____10903)) ->
                               let uu____10908 =
                                 let uu____10913 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____10913) in
                               FStar_Syntax_Syntax.NT uu____10908) formals1
                      binders in
                  let extra_formals1 =
                    let uu____10918 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____10932  ->
                              match uu____10932 with
                              | (x,i) ->
                                  let uu____10939 =
                                    let uu___146_10940 = x in
                                    let uu____10941 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_10940.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_10940.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____10941
                                    } in
                                  (uu____10939, i))) in
                    FStar_All.pipe_right uu____10918
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____10953 =
                      let uu____10955 =
                        let uu____10956 = FStar_Syntax_Subst.subst subst1 t in
                        uu____10956.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____10955 in
                    let uu____10960 =
                      let uu____10961 = FStar_Syntax_Subst.compress body in
                      let uu____10962 =
                        let uu____10963 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____10963 in
                      FStar_Syntax_Syntax.extend_app_n uu____10961
                        uu____10962 in
                    uu____10960 uu____10953 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11005 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11005
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11006 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11006.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11006.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11006.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11006.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11006.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11006.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11006.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11006.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11006.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11006.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11006.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11006.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11006.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11006.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11006.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11006.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11006.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11006.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11006.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11006.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11006.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11006.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11006.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11027 = FStar_Syntax_Util.abs_formals e in
                match uu____11027 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11076::uu____11077 ->
                         let uu____11085 =
                           let uu____11086 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11086.FStar_Syntax_Syntax.n in
                         (match uu____11085 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11113 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11113 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11139 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11139
                                   then
                                     let uu____11157 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11157 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11203  ->
                                                   fun uu____11204  ->
                                                     match (uu____11203,
                                                             uu____11204)
                                                     with
                                                     | ((x,uu____11214),
                                                        (b,uu____11216)) ->
                                                         let uu____11221 =
                                                           let uu____11226 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11226) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11221)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11228 =
                                            let uu____11239 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11239) in
                                          (uu____11228, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11274 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11274 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11326) ->
                              let uu____11331 =
                                let uu____11342 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11342 in
                              (uu____11331, true)
                          | uu____11375 when Prims.op_Negation norm1 ->
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
                          | uu____11377 ->
                              let uu____11378 =
                                let uu____11379 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11380 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11379
                                  uu____11380 in
                              failwith uu____11378)
                     | uu____11393 ->
                         let uu____11394 =
                           let uu____11395 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11395.FStar_Syntax_Syntax.n in
                         (match uu____11394 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11422 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11422 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11440 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11440 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11488 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11516 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11516
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11523 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11564  ->
                            fun lb  ->
                              match uu____11564 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11615 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11615
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11618 =
                                      let uu____11626 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11626
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11618 with
                                    | (tok,decl,env2) ->
                                        let uu____11651 =
                                          let uu____11658 =
                                            let uu____11664 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11664, tok) in
                                          uu____11658 :: toks in
                                        (uu____11651, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11523 with
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
                        | uu____11766 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11771 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11771 vars)
                            else
                              (let uu____11773 =
                                 let uu____11777 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11777) in
                               FStar_SMTEncoding_Util.mkApp uu____11773) in
                      let uu____11782 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11784  ->
                                 match uu___116_11784 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11785 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11788 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11788))) in
                      if uu____11782
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11808;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11810;
                                FStar_Syntax_Syntax.lbeff = uu____11811;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11852 =
                                 let uu____11856 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11856 with
                                 | (tcenv',uu____11867,e_t) ->
                                     let uu____11871 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____11878 -> failwith "Impossible" in
                                     (match uu____11871 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_11887 = env1 in
                                            {
                                              bindings =
                                                (uu___150_11887.bindings);
                                              depth = (uu___150_11887.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_11887.warn);
                                              cache = (uu___150_11887.cache);
                                              nolabels =
                                                (uu___150_11887.nolabels);
                                              use_zfuel_name =
                                                (uu___150_11887.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_11887.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_11887.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11852 with
                                | (env',e1,t_norm1) ->
                                    let uu____11894 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____11894 with
                                     | ((binders,body,uu____11906,uu____11907),curry)
                                         ->
                                         ((let uu____11914 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____11914
                                           then
                                             let uu____11915 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____11916 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____11915 uu____11916
                                           else ());
                                          (let uu____11918 =
                                             encode_binders None binders env' in
                                           match uu____11918 with
                                           | (vars,guards,env'1,binder_decls,uu____11934)
                                               ->
                                               let body1 =
                                                 let uu____11942 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____11942
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____11945 =
                                                 let uu____11950 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____11950
                                                 then
                                                   let uu____11956 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____11957 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____11956, uu____11957)
                                                 else
                                                   (let uu____11963 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____11963)) in
                                               (match uu____11945 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____11977 =
                                                        let uu____11981 =
                                                          let uu____11982 =
                                                            let uu____11988 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____11988) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____11982 in
                                                        let uu____11994 =
                                                          let uu____11996 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____11996 in
                                                        (uu____11981,
                                                          uu____11994,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____11977 in
                                                    let uu____11998 =
                                                      let uu____12000 =
                                                        let uu____12002 =
                                                          let uu____12004 =
                                                            let uu____12006 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12006 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12004 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12002 in
                                                      FStar_List.append
                                                        decls1 uu____12000 in
                                                    (uu____11998, env1))))))
                           | uu____12009 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12028 = varops.fresh "fuel" in
                             (uu____12028, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12031 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12070  ->
                                     fun uu____12071  ->
                                       match (uu____12070, uu____12071) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12153 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12153 in
                                           let gtok =
                                             let uu____12155 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12155 in
                                           let env3 =
                                             let uu____12157 =
                                               let uu____12159 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12159 in
                                             push_free_var env2 flid gtok
                                               uu____12157 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12031 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12245
                                 t_norm uu____12247 =
                                 match (uu____12245, uu____12247) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12274;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12275;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12292 =
                                       let uu____12296 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12296 with
                                       | (tcenv',uu____12311,e_t) ->
                                           let uu____12315 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12322 ->
                                                 failwith "Impossible" in
                                           (match uu____12315 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12331 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12331.bindings);
                                                    depth =
                                                      (uu___151_12331.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12331.warn);
                                                    cache =
                                                      (uu___151_12331.cache);
                                                    nolabels =
                                                      (uu___151_12331.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12331.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12331.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12331.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12292 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12341 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12341
                                            then
                                              let uu____12342 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12343 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12344 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12342 uu____12343
                                                uu____12344
                                            else ());
                                           (let uu____12346 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12346 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12368 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12368
                                                  then
                                                    let uu____12369 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12370 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12371 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12372 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12369 uu____12370
                                                      uu____12371 uu____12372
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12376 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12376 with
                                                  | (vars,guards,env'1,binder_decls,uu____12394)
                                                      ->
                                                      let decl_g =
                                                        let uu____12402 =
                                                          let uu____12408 =
                                                            let uu____12410 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12410 in
                                                          (g, uu____12408,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12402 in
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
                                                        let uu____12425 =
                                                          let uu____12429 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12429) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12425 in
                                                      let gsapp =
                                                        let uu____12435 =
                                                          let uu____12439 =
                                                            let uu____12441 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12441 ::
                                                              vars_tm in
                                                          (g, uu____12439) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12435 in
                                                      let gmax =
                                                        let uu____12445 =
                                                          let uu____12449 =
                                                            let uu____12451 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12451 ::
                                                              vars_tm in
                                                          (g, uu____12449) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12445 in
                                                      let body1 =
                                                        let uu____12455 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12455
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12457 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12457 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12468
                                                               =
                                                               let uu____12472
                                                                 =
                                                                 let uu____12473
                                                                   =
                                                                   let uu____12481
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
                                                                    uu____12481) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12473 in
                                                               let uu____12492
                                                                 =
                                                                 let uu____12494
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12494 in
                                                               (uu____12472,
                                                                 uu____12492,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12468 in
                                                           let eqn_f =
                                                             let uu____12497
                                                               =
                                                               let uu____12501
                                                                 =
                                                                 let uu____12502
                                                                   =
                                                                   let uu____12508
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12508) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12502 in
                                                               (uu____12501,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12497 in
                                                           let eqn_g' =
                                                             let uu____12516
                                                               =
                                                               let uu____12520
                                                                 =
                                                                 let uu____12521
                                                                   =
                                                                   let uu____12527
                                                                    =
                                                                    let uu____12528
                                                                    =
                                                                    let uu____12531
                                                                    =
                                                                    let uu____12532
                                                                    =
                                                                    let uu____12536
                                                                    =
                                                                    let uu____12538
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12538
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12536) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12532 in
                                                                    (gsapp,
                                                                    uu____12531) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12528 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12527) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12521 in
                                                               (uu____12520,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12516 in
                                                           let uu____12550 =
                                                             let uu____12555
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12555
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12572)
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
                                                                    let uu____12587
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12587
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12590
                                                                    =
                                                                    let uu____12594
                                                                    =
                                                                    let uu____12595
                                                                    =
                                                                    let uu____12601
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12601) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12595 in
                                                                    (uu____12594,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12590 in
                                                                 let uu____12612
                                                                   =
                                                                   let uu____12616
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12616
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12624
                                                                    =
                                                                    let uu____12626
                                                                    =
                                                                    let uu____12627
                                                                    =
                                                                    let uu____12631
                                                                    =
                                                                    let uu____12632
                                                                    =
                                                                    let uu____12638
                                                                    =
                                                                    let uu____12639
                                                                    =
                                                                    let uu____12642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12642,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12639 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12638) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12632 in
                                                                    (uu____12631,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12627 in
                                                                    [uu____12626] in
                                                                    (d3,
                                                                    uu____12624) in
                                                                 (match uu____12612
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12550
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
                               let uu____12677 =
                                 let uu____12684 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12720  ->
                                      fun uu____12721  ->
                                        match (uu____12720, uu____12721) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12807 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12807 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12684 in
                               (match uu____12677 with
                                | (decls2,eqns,env01) ->
                                    let uu____12847 =
                                      let isDeclFun uu___117_12855 =
                                        match uu___117_12855 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12856 -> true
                                        | uu____12862 -> false in
                                      let uu____12863 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12863
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12847 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____12890 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____12890
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
        let uu____12923 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____12923 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____12926 = encode_sigelt' env se in
      match uu____12926 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____12936 =
                  let uu____12937 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____12937 in
                [uu____12936]
            | uu____12938 ->
                let uu____12939 =
                  let uu____12941 =
                    let uu____12942 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12942 in
                  uu____12941 :: g in
                let uu____12943 =
                  let uu____12945 =
                    let uu____12946 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____12946 in
                  [uu____12945] in
                FStar_List.append uu____12939 uu____12943 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____12954 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma _
        |FStar_Syntax_Syntax.Sig_main _
         |FStar_Syntax_Syntax.Sig_effect_abbrev _
          |FStar_Syntax_Syntax.Sig_sub_effect _ -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____12963 =
            let uu____12964 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____12964 Prims.op_Negation in
          if uu____12963
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____12984 ->
                   let uu____12985 =
                     let uu____12988 =
                       let uu____12989 =
                         let uu____13004 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13004) in
                       FStar_Syntax_Syntax.Tm_abs uu____12989 in
                     FStar_Syntax_Syntax.mk uu____12988 in
                   uu____12985 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13057 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13057 with
               | (aname,atok,env2) ->
                   let uu____13067 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13067 with
                    | (formals,uu____13077) ->
                        let uu____13084 =
                          let uu____13087 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13087 env2 in
                        (match uu____13084 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13095 =
                                 let uu____13096 =
                                   let uu____13102 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13110  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13102,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13096 in
                               [uu____13095;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13117 =
                               let aux uu____13146 uu____13147 =
                                 match (uu____13146, uu____13147) with
                                 | ((bv,uu____13174),(env3,acc_sorts,acc)) ->
                                     let uu____13195 = gen_term_var env3 bv in
                                     (match uu____13195 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13117 with
                              | (uu____13233,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13247 =
                                      let uu____13251 =
                                        let uu____13252 =
                                          let uu____13258 =
                                            let uu____13259 =
                                              let uu____13262 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13262) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13259 in
                                          ([[app]], xs_sorts, uu____13258) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13252 in
                                      (uu____13251, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13247 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13274 =
                                      let uu____13278 =
                                        let uu____13279 =
                                          let uu____13285 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13285) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13279 in
                                      (uu____13278,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13274 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13295 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13295 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13311,uu____13312)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13313 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13313 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13324,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13329 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13331  ->
                      match uu___118_13331 with
                      | FStar_Syntax_Syntax.Assumption 
                        |FStar_Syntax_Syntax.Projector _
                         |FStar_Syntax_Syntax.Discriminator _
                          |FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13334 -> false)) in
            Prims.op_Negation uu____13329 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13340 = encode_top_level_val env fv t quals in
             match uu____13340 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13352 =
                   let uu____13354 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13354 in
                 (uu____13352, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,f) ->
          let uu____13359 = encode_formula f env in
          (match uu____13359 with
           | (f1,decls) ->
               let g =
                 let uu____13368 =
                   let uu____13369 =
                     let uu____13373 =
                       let uu____13375 =
                         let uu____13376 = FStar_Syntax_Print.lid_to_string l in
                         FStar_Util.format1 "Assumption: %s" uu____13376 in
                       Some uu____13375 in
                     let uu____13377 =
                       varops.mk_unique
                         (Prims.strcat "assumption_" l.FStar_Ident.str) in
                     (f1, uu____13373, uu____13377) in
                   FStar_SMTEncoding_Util.mkAssume uu____13369 in
                 [uu____13368] in
               ((FStar_List.append decls g), env))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13381,uu____13382) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13388 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13395 =
                       let uu____13400 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13400.FStar_Syntax_Syntax.fv_name in
                     uu____13395.FStar_Syntax_Syntax.v in
                   let uu____13404 =
                     let uu____13405 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13405 in
                   if uu____13404
                   then
                     let val_decl =
                       let uu___152_13420 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13420.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13420.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13420.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13424 = encode_sigelt' env1 val_decl in
                     match uu____13424 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13388 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13441,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13443;
                          FStar_Syntax_Syntax.lbtyp = uu____13444;
                          FStar_Syntax_Syntax.lbeff = uu____13445;
                          FStar_Syntax_Syntax.lbdef = uu____13446;_}::[]),uu____13447,uu____13448)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13462 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13462 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13485 =
                   let uu____13487 =
                     let uu____13488 =
                       let uu____13492 =
                         let uu____13493 =
                           let uu____13499 =
                             let uu____13500 =
                               let uu____13503 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13503) in
                             FStar_SMTEncoding_Util.mkEq uu____13500 in
                           ([[b2t_x]], [xx], uu____13499) in
                         FStar_SMTEncoding_Util.mkForall uu____13493 in
                       (uu____13492, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13488 in
                   [uu____13487] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13485 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13520,uu____13521,uu____13522)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13528  ->
                  match uu___119_13528 with
                  | FStar_Syntax_Syntax.Discriminator uu____13529 -> true
                  | uu____13530 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13532,lids,uu____13534) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13541 =
                     let uu____13542 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13542.FStar_Ident.idText in
                   uu____13541 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13544  ->
                     match uu___120_13544 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13545 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13548,uu____13549)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13559  ->
                  match uu___121_13559 with
                  | FStar_Syntax_Syntax.Projector uu____13560 -> true
                  | uu____13563 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13570 = try_lookup_free_var env l in
          (match uu____13570 with
           | Some uu____13574 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13577 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13577.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13577.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13583,uu____13584) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13596) ->
          let uu____13601 = encode_sigelts env ses in
          (match uu____13601 with
           | (g,env1) ->
               let uu____13611 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13621  ->
                         match uu___122_13621 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13622;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13623;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13624;_}
                             -> false
                         | uu____13626 -> true)) in
               (match uu____13611 with
                | (g',inversions) ->
                    let uu____13635 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13645  ->
                              match uu___123_13645 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13646 ->
                                  true
                              | uu____13652 -> false)) in
                    (match uu____13635 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13663,tps,k,uu____13666,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13676  ->
                    match uu___124_13676 with
                    | FStar_Syntax_Syntax.Logic 
                      |FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13677 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13684 = c in
              match uu____13684 with
              | (name,args,uu____13688,uu____13689,uu____13690) ->
                  let uu____13693 =
                    let uu____13694 =
                      let uu____13700 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13707  ->
                                match uu____13707 with
                                | (uu____13711,sort,uu____13713) -> sort)) in
                      (name, uu____13700, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13694 in
                  [uu____13693]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13731 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13734 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13734 FStar_Option.isNone)) in
            if uu____13731
            then []
            else
              (let uu____13751 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13751 with
               | (xxsym,xx) ->
                   let uu____13757 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13768  ->
                             fun l  ->
                               match uu____13768 with
                               | (out,decls) ->
                                   let uu____13780 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13780 with
                                    | (uu____13786,data_t) ->
                                        let uu____13788 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13788 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13817 =
                                                 let uu____13818 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13818.FStar_Syntax_Syntax.n in
                                               match uu____13817 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13826,indices) ->
                                                   indices
                                               | uu____13842 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____13854  ->
                                                         match uu____13854
                                                         with
                                                         | (x,uu____13858) ->
                                                             let uu____13859
                                                               =
                                                               let uu____13860
                                                                 =
                                                                 let uu____13864
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____13864,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____13860 in
                                                             push_term_var
                                                               env1 x
                                                               uu____13859)
                                                    env) in
                                             let uu____13866 =
                                               encode_args indices env1 in
                                             (match uu____13866 with
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
                                                      let uu____13886 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____13894
                                                                 =
                                                                 let uu____13897
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____13897,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____13894)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____13886
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____13899 =
                                                      let uu____13900 =
                                                        let uu____13903 =
                                                          let uu____13904 =
                                                            let uu____13907 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____13907,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____13904 in
                                                        (out, uu____13903) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____13900 in
                                                    (uu____13899,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13757 with
                    | (data_ax,decls) ->
                        let uu____13915 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____13915 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____13926 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____13926 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____13929 =
                                 let uu____13933 =
                                   let uu____13934 =
                                     let uu____13940 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____13948 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____13940,
                                       uu____13948) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____13934 in
                                 let uu____13956 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____13933, (Some "inversion axiom"),
                                   uu____13956) in
                               FStar_SMTEncoding_Util.mkAssume uu____13929 in
                             let pattern_guarded_inversion =
                               let uu____13960 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____13960
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____13968 =
                                   let uu____13969 =
                                     let uu____13973 =
                                       let uu____13974 =
                                         let uu____13980 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____13988 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____13980, uu____13988) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____13974 in
                                     let uu____13996 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____13973, (Some "inversion axiom"),
                                       uu____13996) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____13969 in
                                 [uu____13968]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____13999 =
            let uu____14007 =
              let uu____14008 = FStar_Syntax_Subst.compress k in
              uu____14008.FStar_Syntax_Syntax.n in
            match uu____14007 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14037 -> (tps, k) in
          (match uu____13999 with
           | (formals,res) ->
               let uu____14052 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14052 with
                | (formals1,res1) ->
                    let uu____14059 = encode_binders None formals1 env in
                    (match uu____14059 with
                     | (vars,guards,env',binder_decls,uu____14074) ->
                         let uu____14081 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14081 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14094 =
                                  let uu____14098 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14098) in
                                FStar_SMTEncoding_Util.mkApp uu____14094 in
                              let uu____14103 =
                                let tname_decl =
                                  let uu____14109 =
                                    let uu____14110 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14125  ->
                                              match uu____14125 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14133 = varops.next_id () in
                                    (tname, uu____14110,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14133, false) in
                                  constructor_or_logic_type_decl uu____14109 in
                                let uu____14138 =
                                  match vars with
                                  | [] ->
                                      let uu____14145 =
                                        let uu____14146 =
                                          let uu____14148 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14148 in
                                        push_free_var env1 t tname
                                          uu____14146 in
                                      ([], uu____14145)
                                  | uu____14152 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14158 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14158 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14167 =
                                          let uu____14171 =
                                            let uu____14172 =
                                              let uu____14180 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14180) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14172 in
                                          (uu____14171,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14167 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14138 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14103 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14203 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14203 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14217 =
                                               let uu____14218 =
                                                 let uu____14222 =
                                                   let uu____14223 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14223 in
                                                 (uu____14222,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14218 in
                                             [uu____14217]
                                           else [] in
                                         let uu____14226 =
                                           let uu____14228 =
                                             let uu____14230 =
                                               let uu____14231 =
                                                 let uu____14235 =
                                                   let uu____14236 =
                                                     let uu____14242 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14242) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14236 in
                                                 (uu____14235, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14231 in
                                             [uu____14230] in
                                           FStar_List.append karr uu____14228 in
                                         FStar_List.append decls1 uu____14226 in
                                   let aux =
                                     let uu____14251 =
                                       let uu____14253 =
                                         inversion_axioms tapp vars in
                                       let uu____14255 =
                                         let uu____14257 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14257] in
                                       FStar_List.append uu____14253
                                         uu____14255 in
                                     FStar_List.append kindingAx uu____14251 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14262,uu____14263,uu____14264,uu____14265,uu____14266)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14271,t,uu____14273,n_tps,uu____14275) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14280 = new_term_constant_and_tok_from_lid env d in
          (match uu____14280 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14291 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14291 with
                | (formals,t_res) ->
                    let uu____14313 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14313 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14322 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14322 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14360 =
                                            mk_term_projector_name d x in
                                          (uu____14360,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14362 =
                                  let uu____14372 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14372, true) in
                                FStar_All.pipe_right uu____14362
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
                              let uu____14394 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14394 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14402::uu____14403 ->
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
                                         let uu____14428 =
                                           let uu____14434 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14434) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14428
                                     | uu____14447 -> tok_typing in
                                   let uu____14452 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14452 with
                                    | (vars',guards',env'',decls_formals,uu____14467)
                                        ->
                                        let uu____14474 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14474 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14493 ->
                                                   let uu____14497 =
                                                     let uu____14498 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14498 in
                                                   [uu____14497] in
                                             let encode_elim uu____14505 =
                                               let uu____14506 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14506 with
                                               | (head1,args) ->
                                                   let uu____14535 =
                                                     let uu____14536 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14536.FStar_Syntax_Syntax.n in
                                                   (match uu____14535 with
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
                                                        let uu____14554 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14554
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
                                                                 | uu____14580
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14588
                                                                    =
                                                                    let uu____14589
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14589 in
                                                                    if
                                                                    uu____14588
                                                                    then
                                                                    let uu____14596
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14596]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14598
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14611
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14611
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14633
                                                                    =
                                                                    let uu____14637
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14637 in
                                                                    (match uu____14633
                                                                    with
                                                                    | 
                                                                    (uu____14644,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14650
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14650
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14652
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14652
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
                                                             (match uu____14598
                                                              with
                                                              | (uu____14660,arg_vars,elim_eqns_or_guards,uu____14663)
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
                                                                    let uu____14682
                                                                    =
                                                                    let uu____14686
                                                                    =
                                                                    let uu____14687
                                                                    =
                                                                    let uu____14693
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14699
                                                                    =
                                                                    let uu____14700
                                                                    =
                                                                    let uu____14703
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14703) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14700 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14693,
                                                                    uu____14699) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14687 in
                                                                    (uu____14686,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14682 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14716
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14716,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14718
                                                                    =
                                                                    let uu____14722
                                                                    =
                                                                    let uu____14723
                                                                    =
                                                                    let uu____14729
                                                                    =
                                                                    let uu____14732
                                                                    =
                                                                    let uu____14734
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14734] in
                                                                    [uu____14732] in
                                                                    let uu____14737
                                                                    =
                                                                    let uu____14738
                                                                    =
                                                                    let uu____14741
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14742
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14741,
                                                                    uu____14742) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14738 in
                                                                    (uu____14729,
                                                                    [x],
                                                                    uu____14737) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14723 in
                                                                    let uu____14752
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14722,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14752) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14718
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14757
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
                                                                    (let uu____14772
                                                                    =
                                                                    let uu____14773
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14773
                                                                    dapp1 in
                                                                    [uu____14772]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14757
                                                                    FStar_List.flatten in
                                                                    let uu____14777
                                                                    =
                                                                    let uu____14781
                                                                    =
                                                                    let uu____14782
                                                                    =
                                                                    let uu____14788
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14794
                                                                    =
                                                                    let uu____14795
                                                                    =
                                                                    let uu____14798
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14798) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14795 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14788,
                                                                    uu____14794) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14782 in
                                                                    (uu____14781,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14777) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____14808 ->
                                                        ((let uu____14810 =
                                                            let uu____14811 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____14812 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____14811
                                                              uu____14812 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____14810);
                                                         ([], []))) in
                                             let uu____14815 = encode_elim () in
                                             (match uu____14815 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____14827 =
                                                      let uu____14829 =
                                                        let uu____14831 =
                                                          let uu____14833 =
                                                            let uu____14835 =
                                                              let uu____14836
                                                                =
                                                                let uu____14842
                                                                  =
                                                                  let uu____14844
                                                                    =
                                                                    let uu____14845
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____14845 in
                                                                  Some
                                                                    uu____14844 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____14842) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____14836 in
                                                            [uu____14835] in
                                                          let uu____14848 =
                                                            let uu____14850 =
                                                              let uu____14852
                                                                =
                                                                let uu____14854
                                                                  =
                                                                  let uu____14856
                                                                    =
                                                                    let uu____14858
                                                                    =
                                                                    let uu____14860
                                                                    =
                                                                    let uu____14861
                                                                    =
                                                                    let uu____14865
                                                                    =
                                                                    let uu____14866
                                                                    =
                                                                    let uu____14872
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____14872) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14866 in
                                                                    (uu____14865,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14861 in
                                                                    let uu____14879
                                                                    =
                                                                    let uu____14881
                                                                    =
                                                                    let uu____14882
                                                                    =
                                                                    let uu____14886
                                                                    =
                                                                    let uu____14887
                                                                    =
                                                                    let uu____14893
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____14899
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____14893,
                                                                    uu____14899) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14887 in
                                                                    (uu____14886,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14882 in
                                                                    [uu____14881] in
                                                                    uu____14860
                                                                    ::
                                                                    uu____14879 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____14858 in
                                                                  FStar_List.append
                                                                    uu____14856
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____14854 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____14852 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____14850 in
                                                          FStar_List.append
                                                            uu____14833
                                                            uu____14848 in
                                                        FStar_List.append
                                                          decls3 uu____14831 in
                                                      FStar_List.append
                                                        decls2 uu____14829 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____14827 in
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
           (fun uu____14920  ->
              fun se  ->
                match uu____14920 with
                | (g,env1) ->
                    let uu____14932 = encode_sigelt env1 se in
                    (match uu____14932 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____14968 =
        match uu____14968 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____14986 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____14991 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____14991
                   then
                     let uu____14992 = FStar_Syntax_Print.bv_to_string x in
                     let uu____14993 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____14994 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____14992 uu____14993 uu____14994
                   else ());
                  (let uu____14996 = encode_term t1 env1 in
                   match uu____14996 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15006 =
                         let uu____15010 =
                           let uu____15011 =
                             let uu____15012 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15012
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15011 in
                         new_term_constant_from_string env1 x uu____15010 in
                       (match uu____15006 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15023 = FStar_Options.log_queries () in
                              if uu____15023
                              then
                                let uu____15025 =
                                  let uu____15026 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15027 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15028 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15026 uu____15027 uu____15028 in
                                Some uu____15025
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15039,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15048 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15048 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst (_,se,_)
               |FStar_TypeChecker_Env.Binding_sig (_,se) ->
                 let uu____15067 = encode_sigelt env1 se in
                 (match uu____15067 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15077 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15077 with | (uu____15089,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15134  ->
            match uu____15134 with
            | (l,uu____15141,uu____15142) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15163  ->
            match uu____15163 with
            | (l,uu____15171,uu____15172) ->
                let uu____15177 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15178 =
                  let uu____15180 =
                    let uu____15181 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15181 in
                  [uu____15180] in
                uu____15177 :: uu____15178)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15192 =
      let uu____15194 =
        let uu____15195 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15197 =
          let uu____15198 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15198 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15195;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15197
        } in
      [uu____15194] in
    FStar_ST.write last_env uu____15192
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15208 = FStar_ST.read last_env in
      match uu____15208 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15214 ->
          let uu___154_15216 = e in
          let uu____15217 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15216.bindings);
            depth = (uu___154_15216.depth);
            tcenv;
            warn = (uu___154_15216.warn);
            cache = (uu___154_15216.cache);
            nolabels = (uu___154_15216.nolabels);
            use_zfuel_name = (uu___154_15216.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15216.encode_non_total_function_typ);
            current_module_name = uu____15217
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15221 = FStar_ST.read last_env in
    match uu____15221 with
    | [] -> failwith "Empty env stack"
    | uu____15226::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15234  ->
    let uu____15235 = FStar_ST.read last_env in
    match uu____15235 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15246 = hd1 in
          {
            bindings = (uu___155_15246.bindings);
            depth = (uu___155_15246.depth);
            tcenv = (uu___155_15246.tcenv);
            warn = (uu___155_15246.warn);
            cache = refs;
            nolabels = (uu___155_15246.nolabels);
            use_zfuel_name = (uu___155_15246.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15246.encode_non_total_function_typ);
            current_module_name = (uu___155_15246.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15252  ->
    let uu____15253 = FStar_ST.read last_env in
    match uu____15253 with
    | [] -> failwith "Popping an empty stack"
    | uu____15258::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15266  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15269  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15272  ->
    let uu____15273 = FStar_ST.read last_env in
    match uu____15273 with
    | hd1::uu____15279::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15285 -> failwith "Impossible"
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
        | (uu____15334::uu____15335,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15339 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15339.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15339.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15339.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15340 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15351 =
        let uu____15353 =
          let uu____15354 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15354 in
        let uu____15355 = open_fact_db_tags env in uu____15353 :: uu____15355 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15351
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
      let uu____15370 = encode_sigelt env se in
      match uu____15370 with
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
        let uu____15395 = FStar_Options.log_queries () in
        if uu____15395
        then
          let uu____15397 =
            let uu____15398 =
              let uu____15399 =
                let uu____15400 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15400 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15399 in
            FStar_SMTEncoding_Term.Caption uu____15398 in
          uu____15397 :: decls
        else decls in
      let env =
        let uu____15407 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15407 tcenv in
      let uu____15408 = encode_top_level_facts env se in
      match uu____15408 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15417 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15417))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15428 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15428
       then
         let uu____15429 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15429
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15450  ->
                 fun se  ->
                   match uu____15450 with
                   | (g,env2) ->
                       let uu____15462 = encode_top_level_facts env2 se in
                       (match uu____15462 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15475 =
         encode_signature
           (let uu___157_15479 = env in
            {
              bindings = (uu___157_15479.bindings);
              depth = (uu___157_15479.depth);
              tcenv = (uu___157_15479.tcenv);
              warn = false;
              cache = (uu___157_15479.cache);
              nolabels = (uu___157_15479.nolabels);
              use_zfuel_name = (uu___157_15479.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15479.encode_non_total_function_typ);
              current_module_name = (uu___157_15479.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15475 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15491 = FStar_Options.log_queries () in
             if uu____15491
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15496 = env1 in
               {
                 bindings = (uu___158_15496.bindings);
                 depth = (uu___158_15496.depth);
                 tcenv = (uu___158_15496.tcenv);
                 warn = true;
                 cache = (uu___158_15496.cache);
                 nolabels = (uu___158_15496.nolabels);
                 use_zfuel_name = (uu___158_15496.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15496.encode_non_total_function_typ);
                 current_module_name = (uu___158_15496.current_module_name)
               });
            (let uu____15498 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15498
             then FStar_Util.print1 "Done encoding externals for %s\n" name
             else ());
            (let decls1 = caption decls in FStar_SMTEncoding_Z3.giveZ3 decls1)))
let encode_query:
  (Prims.unit -> Prims.string) option ->
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
        (let uu____15533 =
           let uu____15534 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15534.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15533);
        (let env =
           let uu____15536 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15536 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15543 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15564 = aux rest in
                 (match uu____15564 with
                  | (out,rest1) ->
                      let t =
                        let uu____15582 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____15582 with
                        | Some uu____15586 ->
                            let uu____15587 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____15587
                              x.FStar_Syntax_Syntax.sort
                        | uu____15588 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____15591 =
                        let uu____15593 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_15594 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_15594.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_15594.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____15593 :: out in
                      (uu____15591, rest1))
             | uu____15597 -> ([], bindings1) in
           let uu____15601 = aux bindings in
           match uu____15601 with
           | (closing,bindings1) ->
               let uu____15615 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____15615, bindings1) in
         match uu____15543 with
         | (q1,bindings1) ->
             let uu____15628 =
               let uu____15631 =
                 FStar_List.filter
                   (fun uu___125_15633  ->
                      match uu___125_15633 with
                      | FStar_TypeChecker_Env.Binding_sig uu____15634 ->
                          false
                      | uu____15638 -> true) bindings1 in
               encode_env_bindings env uu____15631 in
             (match uu____15628 with
              | (env_decls,env1) ->
                  ((let uu____15649 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____15649
                    then
                      let uu____15650 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____15650
                    else ());
                   (let uu____15652 = encode_formula q1 env1 in
                    match uu____15652 with
                    | (phi,qdecls) ->
                        let uu____15664 =
                          let uu____15667 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____15667 phi in
                        (match uu____15664 with
                         | (labels,phi1) ->
                             let uu____15677 = encode_labels labels in
                             (match uu____15677 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____15698 =
                                      let uu____15702 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____15703 =
                                        varops.mk_unique "@query" in
                                      (uu____15702, (Some "query"),
                                        uu____15703) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____15698 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____15716 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15716 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____15718 = encode_formula q env in
       match uu____15718 with
       | (f,uu____15722) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____15724) -> true
             | uu____15727 -> false)))