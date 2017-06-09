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
      | FStar_Syntax_Syntax.Tm_arrow uu____1651 -> true
      | FStar_Syntax_Syntax.Tm_refine uu____1659 -> true
      | FStar_Syntax_Syntax.Tm_bvar uu____1664 -> true
      | FStar_Syntax_Syntax.Tm_uvar uu____1665 -> true
      | FStar_Syntax_Syntax.Tm_abs uu____1676 -> true
      | FStar_Syntax_Syntax.Tm_constant uu____1691 -> true
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1693 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1693 FStar_Option.isNone
      | FStar_Syntax_Syntax.Tm_app
          ({ FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_fvar fv;
             FStar_Syntax_Syntax.tk = uu____1707;
             FStar_Syntax_Syntax.pos = uu____1708;
             FStar_Syntax_Syntax.vars = uu____1709;_},uu____1710)
          ->
          let uu____1725 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1725 FStar_Option.isNone
      | uu____1738 -> false
let head_redex: env_t -> FStar_Syntax_Syntax.term -> Prims.bool =
  fun env  ->
    fun t  ->
      let uu____1745 =
        let uu____1746 = FStar_Syntax_Util.un_uinst t in
        uu____1746.FStar_Syntax_Syntax.n in
      match uu____1745 with
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1749,uu____1750,Some (FStar_Util.Inr (l,flags))) ->
          ((FStar_Ident.lid_equals l FStar_Syntax_Const.effect_Tot_lid) ||
             (FStar_Ident.lid_equals l FStar_Syntax_Const.effect_GTot_lid))
            ||
            (FStar_List.existsb
               (fun uu___108_1779  ->
                  match uu___108_1779 with
                  | FStar_Syntax_Syntax.TOTAL  -> true
                  | uu____1780 -> false) flags)
      | FStar_Syntax_Syntax.Tm_abs
          (uu____1781,uu____1782,Some (FStar_Util.Inl lc)) ->
          FStar_Syntax_Util.is_tot_or_gtot_lcomp lc
      | FStar_Syntax_Syntax.Tm_fvar fv ->
          let uu____1809 =
            FStar_TypeChecker_Env.lookup_definition
              [FStar_TypeChecker_Env.Eager_unfolding_only] env.tcenv
              (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          FStar_All.pipe_right uu____1809 FStar_Option.isSome
      | uu____1822 -> false
let whnf: env_t -> FStar_Syntax_Syntax.term -> FStar_Syntax_Syntax.term =
  fun env  ->
    fun t  ->
      let uu____1829 = head_normal env t in
      if uu____1829
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
    let uu____1840 =
      let uu____1841 = FStar_Syntax_Syntax.null_binder t in [uu____1841] in
    let uu____1842 =
      FStar_Syntax_Syntax.fvar FStar_Syntax_Const.true_lid
        FStar_Syntax_Syntax.Delta_constant None in
    FStar_Syntax_Util.abs uu____1840 uu____1842 None
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
                    let uu____1869 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Term.mk_ApplyTF out uu____1869
                | s ->
                    let uu____1872 = FStar_SMTEncoding_Util.mkFreeV var in
                    FStar_SMTEncoding_Util.mk_ApplyTT out uu____1872) e)
let mk_Apply_args:
  FStar_SMTEncoding_Term.term ->
    FStar_SMTEncoding_Term.term Prims.list -> FStar_SMTEncoding_Term.term
  =
  fun e  ->
    fun args  ->
      FStar_All.pipe_right args
        (FStar_List.fold_left FStar_SMTEncoding_Util.mk_ApplyTT e)
let is_app: FStar_SMTEncoding_Term.op -> Prims.bool =
  fun uu___109_1884  ->
    match uu___109_1884 with
    | FStar_SMTEncoding_Term.Var "ApplyTT" -> true
    | FStar_SMTEncoding_Term.Var "ApplyTF" -> true
    | uu____1885 -> false
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
                       FStar_SMTEncoding_Term.freevars = uu____1913;
                       FStar_SMTEncoding_Term.rng = uu____1914;_}::[]),x::xs1)
              when (is_app app) && (FStar_SMTEncoding_Term.fv_eq x y) ->
              check_partial_applications f xs1
          | (FStar_SMTEncoding_Term.App
             (FStar_SMTEncoding_Term.Var f,args),uu____1928) ->
              let uu____1933 =
                ((FStar_List.length args) = (FStar_List.length xs)) &&
                  (FStar_List.forall2
                     (fun a  ->
                        fun v1  ->
                          match a.FStar_SMTEncoding_Term.tm with
                          | FStar_SMTEncoding_Term.FreeV fv ->
                              FStar_SMTEncoding_Term.fv_eq fv v1
                          | uu____1943 -> false) args (FStar_List.rev xs)) in
              if uu____1933 then tok_of_name env f else None
          | (uu____1946,[]) ->
              let fvs = FStar_SMTEncoding_Term.free_variables t in
              let uu____1949 =
                FStar_All.pipe_right fvs
                  (FStar_List.for_all
                     (fun fv  ->
                        let uu____1951 =
                          FStar_Util.for_some
                            (FStar_SMTEncoding_Term.fv_eq fv) vars in
                        Prims.op_Negation uu____1951)) in
              if uu____1949 then Some t else None
          | uu____1954 -> None in
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
    | uu____2038 -> false
let encode_const: FStar_Const.sconst -> FStar_SMTEncoding_Term.term =
  fun uu___110_2041  ->
    match uu___110_2041 with
    | FStar_Const.Const_unit  -> FStar_SMTEncoding_Term.mk_Term_unit
    | FStar_Const.Const_bool (true ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkTrue
    | FStar_Const.Const_bool (false ) ->
        FStar_SMTEncoding_Term.boxBool FStar_SMTEncoding_Util.mkFalse
    | FStar_Const.Const_char c ->
        let uu____2043 =
          let uu____2047 =
            let uu____2049 =
              let uu____2050 =
                FStar_SMTEncoding_Util.mkInteger' (FStar_Util.int_of_char c) in
              FStar_SMTEncoding_Term.boxInt uu____2050 in
            [uu____2049] in
          ("FStar.Char.Char", uu____2047) in
        FStar_SMTEncoding_Util.mkApp uu____2043
    | FStar_Const.Const_int (i,None ) ->
        let uu____2058 = FStar_SMTEncoding_Util.mkInteger i in
        FStar_SMTEncoding_Term.boxInt uu____2058
    | FStar_Const.Const_int (i,Some uu____2060) ->
        failwith "Machine integers should be desugared"
    | FStar_Const.Const_string (bytes,uu____2069) ->
        let uu____2072 = FStar_All.pipe_left FStar_Util.string_of_bytes bytes in
        varops.string_const uu____2072
    | FStar_Const.Const_range r -> FStar_SMTEncoding_Term.mk_Range_const
    | FStar_Const.Const_effect  -> FStar_SMTEncoding_Term.mk_Term_type
    | c ->
        let uu____2076 =
          let uu____2077 = FStar_Syntax_Print.const_to_string c in
          FStar_Util.format1 "Unhandled constant: %s" uu____2077 in
        failwith uu____2076
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
        | FStar_Syntax_Syntax.Tm_arrow uu____2096 -> t1
        | FStar_Syntax_Syntax.Tm_refine uu____2104 ->
            let uu____2109 = FStar_Syntax_Util.unrefine t1 in
            aux true uu____2109
        | uu____2110 ->
            if norm1
            then let uu____2111 = whnf env t1 in aux false uu____2111
            else
              (let uu____2113 =
                 let uu____2114 =
                   FStar_Range.string_of_range t0.FStar_Syntax_Syntax.pos in
                 let uu____2115 = FStar_Syntax_Print.term_to_string t0 in
                 FStar_Util.format2 "(%s) Expected a function typ; got %s"
                   uu____2114 uu____2115 in
               failwith uu____2113) in
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
    | uu____2136 ->
        let uu____2137 = FStar_Syntax_Syntax.mk_Total k1 in ([], uu____2137)
let is_arithmetic_primitive head1 args =
  match ((head1.FStar_Syntax_Syntax.n), args) with
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2165::uu____2166::[]) ->
      ((((FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Addition) ||
           (FStar_Syntax_Syntax.fv_eq_lid fv
              FStar_Syntax_Const.op_Subtraction))
          ||
          (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Multiply))
         || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Division))
        || (FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Modulus)
  | (FStar_Syntax_Syntax.Tm_fvar fv,uu____2169::[]) ->
      FStar_Syntax_Syntax.fv_eq_lid fv FStar_Syntax_Const.op_Minus
  | uu____2171 -> false
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
        (let uu____2309 =
           FStar_TypeChecker_Env.debug env.tcenv FStar_Options.Low in
         if uu____2309
         then
           let uu____2310 = FStar_Syntax_Print.binders_to_string ", " bs in
           FStar_Util.print1 "Encoding binders %s\n" uu____2310
         else ());
        (let uu____2312 =
           FStar_All.pipe_right bs
             (FStar_List.fold_left
                (fun uu____2348  ->
                   fun b  ->
                     match uu____2348 with
                     | (vars,guards,env1,decls,names1) ->
                         let uu____2391 =
                           let x = unmangle (fst b) in
                           let uu____2400 = gen_term_var env1 x in
                           match uu____2400 with
                           | (xxsym,xx,env') ->
                               let uu____2414 =
                                 let uu____2417 =
                                   norm env1 x.FStar_Syntax_Syntax.sort in
                                 encode_term_pred fuel_opt uu____2417 env1 xx in
                               (match uu____2414 with
                                | (guard_x_t,decls') ->
                                    ((xxsym,
                                       FStar_SMTEncoding_Term.Term_sort),
                                      guard_x_t, env', decls', x)) in
                         (match uu____2391 with
                          | (v1,g,env2,decls',n1) ->
                              ((v1 :: vars), (g :: guards), env2,
                                (FStar_List.append decls decls'), (n1 ::
                                names1)))) ([], [], env, [], [])) in
         match uu____2312 with
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
          let uu____2505 = encode_term t env in
          match uu____2505 with
          | (t1,decls) ->
              let uu____2512 =
                FStar_SMTEncoding_Term.mk_HasTypeWithFuel fuel_opt e t1 in
              (uu____2512, decls)
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
          let uu____2520 = encode_term t env in
          match uu____2520 with
          | (t1,decls) ->
              (match fuel_opt with
               | None  ->
                   let uu____2529 = FStar_SMTEncoding_Term.mk_HasTypeZ e t1 in
                   (uu____2529, decls)
               | Some f ->
                   let uu____2531 =
                     FStar_SMTEncoding_Term.mk_HasTypeFuel f e t1 in
                   (uu____2531, decls))
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
        let uu____2537 = encode_args args_e env in
        match uu____2537 with
        | (arg_tms,decls) ->
            let head_fv =
              match head1.FStar_Syntax_Syntax.n with
              | FStar_Syntax_Syntax.Tm_fvar fv -> fv
              | uu____2549 -> failwith "Impossible" in
            let unary arg_tms1 =
              let uu____2556 = FStar_List.hd arg_tms1 in
              FStar_SMTEncoding_Term.unboxInt uu____2556 in
            let binary arg_tms1 =
              let uu____2565 =
                let uu____2566 = FStar_List.hd arg_tms1 in
                FStar_SMTEncoding_Term.unboxInt uu____2566 in
              let uu____2567 =
                let uu____2568 =
                  let uu____2569 = FStar_List.tl arg_tms1 in
                  FStar_List.hd uu____2569 in
                FStar_SMTEncoding_Term.unboxInt uu____2568 in
              (uu____2565, uu____2567) in
            let mk_default uu____2574 =
              let uu____2575 =
                lookup_free_var_sym env head_fv.FStar_Syntax_Syntax.fv_name in
              match uu____2575 with
              | (fname,fuel_args) ->
                  FStar_SMTEncoding_Util.mkApp'
                    (fname, (FStar_List.append fuel_args arg_tms)) in
            let mk_l op mk_args ts =
              let uu____2620 = FStar_Options.smtencoding_l_arith_native () in
              if uu____2620
              then
                let uu____2621 = let uu____2622 = mk_args ts in op uu____2622 in
                FStar_All.pipe_right uu____2621 FStar_SMTEncoding_Term.boxInt
              else mk_default () in
            let mk_nl nm op ts =
              let uu____2645 = FStar_Options.smtencoding_nl_arith_wrapped () in
              if uu____2645
              then
                let uu____2646 = binary ts in
                match uu____2646 with
                | (t1,t2) ->
                    let uu____2651 =
                      FStar_SMTEncoding_Util.mkApp (nm, [t1; t2]) in
                    FStar_All.pipe_right uu____2651
                      FStar_SMTEncoding_Term.boxInt
              else
                (let uu____2654 =
                   FStar_Options.smtencoding_nl_arith_native () in
                 if uu____2654
                 then
                   let uu____2655 = op (binary ts) in
                   FStar_All.pipe_right uu____2655
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
            let uu____2745 =
              let uu____2751 =
                FStar_List.tryFind
                  (fun uu____2763  ->
                     match uu____2763 with
                     | (l,uu____2770) ->
                         FStar_Syntax_Syntax.fv_eq_lid head_fv l) ops in
              FStar_All.pipe_right uu____2751 FStar_Util.must in
            (match uu____2745 with
             | (uu____2795,op) ->
                 let uu____2803 = op arg_tms in (uu____2803, decls))
and encode_term:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let t0 = FStar_Syntax_Subst.compress t in
      (let uu____2810 =
         FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
           (FStar_Options.Other "SMTEncoding") in
       if uu____2810
       then
         let uu____2811 = FStar_Syntax_Print.tag_of_term t in
         let uu____2812 = FStar_Syntax_Print.tag_of_term t0 in
         let uu____2813 = FStar_Syntax_Print.term_to_string t0 in
         FStar_Util.print3 "(%s) (%s)   %s\n" uu____2811 uu____2812
           uu____2813
       else ());
      (match t0.FStar_Syntax_Syntax.n with
       | FStar_Syntax_Syntax.Tm_delayed uu____2817 ->
           let uu____2838 =
             let uu____2839 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2840 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2841 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2842 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2839
               uu____2840 uu____2841 uu____2842 in
           failwith uu____2838
       | FStar_Syntax_Syntax.Tm_unknown  ->
           let uu____2845 =
             let uu____2846 =
               FStar_All.pipe_left FStar_Range.string_of_range
                 t.FStar_Syntax_Syntax.pos in
             let uu____2847 = FStar_Syntax_Print.tag_of_term t0 in
             let uu____2848 = FStar_Syntax_Print.term_to_string t0 in
             let uu____2849 = FStar_Syntax_Print.term_to_string t in
             FStar_Util.format4 "(%s) Impossible: %s\n%s\n%s\n" uu____2846
               uu____2847 uu____2848 uu____2849 in
           failwith uu____2845
       | FStar_Syntax_Syntax.Tm_bvar x ->
           let uu____2853 =
             let uu____2854 = FStar_Syntax_Print.bv_to_string x in
             FStar_Util.format1 "Impossible: locally nameless; got %s"
               uu____2854 in
           failwith uu____2853
       | FStar_Syntax_Syntax.Tm_ascribed (t1,k,uu____2859) ->
           encode_term t1 env
       | FStar_Syntax_Syntax.Tm_meta (t1,uu____2889) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_name x ->
           let t1 = lookup_term_var env x in (t1, [])
       | FStar_Syntax_Syntax.Tm_fvar v1 ->
           let uu____2898 =
             lookup_free_var env v1.FStar_Syntax_Syntax.fv_name in
           (uu____2898, [])
       | FStar_Syntax_Syntax.Tm_type uu____2904 ->
           (FStar_SMTEncoding_Term.mk_Term_type, [])
       | FStar_Syntax_Syntax.Tm_uinst (t1,uu____2907) -> encode_term t1 env
       | FStar_Syntax_Syntax.Tm_constant c ->
           let uu____2913 = encode_const c in (uu____2913, [])
       | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
           let module_name = env.current_module_name in
           let uu____2928 = FStar_Syntax_Subst.open_comp binders c in
           (match uu____2928 with
            | (binders1,res) ->
                let uu____2935 =
                  (env.encode_non_total_function_typ &&
                     (FStar_Syntax_Util.is_pure_or_ghost_comp res))
                    || (FStar_Syntax_Util.is_tot_or_gtot_comp res) in
                if uu____2935
                then
                  let uu____2938 = encode_binders None binders1 env in
                  (match uu____2938 with
                   | (vars,guards,env',decls,uu____2953) ->
                       let fsym =
                         let uu____2963 = varops.fresh "f" in
                         (uu____2963, FStar_SMTEncoding_Term.Term_sort) in
                       let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                       let app = mk_Apply f vars in
                       let uu____2966 =
                         FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                           (let uu___135_2970 = env.tcenv in
                            {
                              FStar_TypeChecker_Env.solver =
                                (uu___135_2970.FStar_TypeChecker_Env.solver);
                              FStar_TypeChecker_Env.range =
                                (uu___135_2970.FStar_TypeChecker_Env.range);
                              FStar_TypeChecker_Env.curmodule =
                                (uu___135_2970.FStar_TypeChecker_Env.curmodule);
                              FStar_TypeChecker_Env.gamma =
                                (uu___135_2970.FStar_TypeChecker_Env.gamma);
                              FStar_TypeChecker_Env.gamma_cache =
                                (uu___135_2970.FStar_TypeChecker_Env.gamma_cache);
                              FStar_TypeChecker_Env.modules =
                                (uu___135_2970.FStar_TypeChecker_Env.modules);
                              FStar_TypeChecker_Env.expected_typ =
                                (uu___135_2970.FStar_TypeChecker_Env.expected_typ);
                              FStar_TypeChecker_Env.sigtab =
                                (uu___135_2970.FStar_TypeChecker_Env.sigtab);
                              FStar_TypeChecker_Env.is_pattern =
                                (uu___135_2970.FStar_TypeChecker_Env.is_pattern);
                              FStar_TypeChecker_Env.instantiate_imp =
                                (uu___135_2970.FStar_TypeChecker_Env.instantiate_imp);
                              FStar_TypeChecker_Env.effects =
                                (uu___135_2970.FStar_TypeChecker_Env.effects);
                              FStar_TypeChecker_Env.generalize =
                                (uu___135_2970.FStar_TypeChecker_Env.generalize);
                              FStar_TypeChecker_Env.letrecs =
                                (uu___135_2970.FStar_TypeChecker_Env.letrecs);
                              FStar_TypeChecker_Env.top_level =
                                (uu___135_2970.FStar_TypeChecker_Env.top_level);
                              FStar_TypeChecker_Env.check_uvars =
                                (uu___135_2970.FStar_TypeChecker_Env.check_uvars);
                              FStar_TypeChecker_Env.use_eq =
                                (uu___135_2970.FStar_TypeChecker_Env.use_eq);
                              FStar_TypeChecker_Env.is_iface =
                                (uu___135_2970.FStar_TypeChecker_Env.is_iface);
                              FStar_TypeChecker_Env.admit =
                                (uu___135_2970.FStar_TypeChecker_Env.admit);
                              FStar_TypeChecker_Env.lax = true;
                              FStar_TypeChecker_Env.lax_universes =
                                (uu___135_2970.FStar_TypeChecker_Env.lax_universes);
                              FStar_TypeChecker_Env.type_of =
                                (uu___135_2970.FStar_TypeChecker_Env.type_of);
                              FStar_TypeChecker_Env.universe_of =
                                (uu___135_2970.FStar_TypeChecker_Env.universe_of);
                              FStar_TypeChecker_Env.use_bv_sorts =
                                (uu___135_2970.FStar_TypeChecker_Env.use_bv_sorts);
                              FStar_TypeChecker_Env.qname_and_index =
                                (uu___135_2970.FStar_TypeChecker_Env.qname_and_index)
                            }) res in
                       (match uu____2966 with
                        | (pre_opt,res_t) ->
                            let uu____2977 =
                              encode_term_pred None res_t env' app in
                            (match uu____2977 with
                             | (res_pred,decls') ->
                                 let uu____2984 =
                                   match pre_opt with
                                   | None  ->
                                       let uu____2991 =
                                         FStar_SMTEncoding_Util.mk_and_l
                                           guards in
                                       (uu____2991, [])
                                   | Some pre ->
                                       let uu____2994 =
                                         encode_formula pre env' in
                                       (match uu____2994 with
                                        | (guard,decls0) ->
                                            let uu____3002 =
                                              FStar_SMTEncoding_Util.mk_and_l
                                                (guard :: guards) in
                                            (uu____3002, decls0)) in
                                 (match uu____2984 with
                                  | (guards1,guard_decls) ->
                                      let t_interp =
                                        let uu____3010 =
                                          let uu____3016 =
                                            FStar_SMTEncoding_Util.mkImp
                                              (guards1, res_pred) in
                                          ([[app]], vars, uu____3016) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____3010 in
                                      let cvars =
                                        let uu____3026 =
                                          FStar_SMTEncoding_Term.free_variables
                                            t_interp in
                                        FStar_All.pipe_right uu____3026
                                          (FStar_List.filter
                                             (fun uu____3032  ->
                                                match uu____3032 with
                                                | (x,uu____3036) ->
                                                    x <> (fst fsym))) in
                                      let tkey =
                                        FStar_SMTEncoding_Util.mkForall
                                          ([], (fsym :: cvars), t_interp) in
                                      let tkey_hash =
                                        FStar_SMTEncoding_Term.hash_of_term
                                          tkey in
                                      let uu____3047 =
                                        FStar_Util.smap_try_find env.cache
                                          tkey_hash in
                                      (match uu____3047 with
                                       | Some cache_entry ->
                                           let uu____3052 =
                                             let uu____3053 =
                                               let uu____3057 =
                                                 FStar_All.pipe_right cvars
                                                   (FStar_List.map
                                                      FStar_SMTEncoding_Util.mkFreeV) in
                                               ((cache_entry.cache_symbol_name),
                                                 uu____3057) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3053 in
                                           (uu____3052,
                                             (FStar_List.append decls
                                                (FStar_List.append decls'
                                                   (FStar_List.append
                                                      guard_decls
                                                      (use_cache_entry
                                                         cache_entry)))))
                                       | None  ->
                                           let tsym =
                                             let uu____3068 =
                                               let uu____3069 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "Tm_arrow_"
                                                 uu____3069 in
                                             varops.mk_unique uu____3068 in
                                           let cvar_sorts =
                                             FStar_List.map
                                               FStar_Pervasives.snd cvars in
                                           let caption =
                                             let uu____3076 =
                                               FStar_Options.log_queries () in
                                             if uu____3076
                                             then
                                               let uu____3078 =
                                                 FStar_TypeChecker_Normalize.term_to_string
                                                   env.tcenv t0 in
                                               Some uu____3078
                                             else None in
                                           let tdecl =
                                             FStar_SMTEncoding_Term.DeclFun
                                               (tsym, cvar_sorts,
                                                 FStar_SMTEncoding_Term.Term_sort,
                                                 caption) in
                                           let t1 =
                                             let uu____3084 =
                                               let uu____3088 =
                                                 FStar_List.map
                                                   FStar_SMTEncoding_Util.mkFreeV
                                                   cvars in
                                               (tsym, uu____3088) in
                                             FStar_SMTEncoding_Util.mkApp
                                               uu____3084 in
                                           let t_has_kind =
                                             FStar_SMTEncoding_Term.mk_HasType
                                               t1
                                               FStar_SMTEncoding_Term.mk_Term_type in
                                           let k_assumption =
                                             let a_name =
                                               Prims.strcat "kinding_" tsym in
                                             let uu____3096 =
                                               let uu____3100 =
                                                 FStar_SMTEncoding_Util.mkForall
                                                   ([[t_has_kind]], cvars,
                                                     t_has_kind) in
                                               (uu____3100, (Some a_name),
                                                 a_name) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3096 in
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
                                             let uu____3113 =
                                               let uu____3117 =
                                                 let uu____3118 =
                                                   let uu____3124 =
                                                     let uu____3125 =
                                                       let uu____3128 =
                                                         let uu____3129 =
                                                           FStar_SMTEncoding_Term.mk_PreType
                                                             f in
                                                         FStar_SMTEncoding_Term.mk_tester
                                                           "Tm_arrow"
                                                           uu____3129 in
                                                       (f_has_t, uu____3128) in
                                                     FStar_SMTEncoding_Util.mkImp
                                                       uu____3125 in
                                                   ([[f_has_t]], (fsym ::
                                                     cvars), uu____3124) in
                                                 mkForall_fuel uu____3118 in
                                               (uu____3117,
                                                 (Some
                                                    "pre-typing for functions"),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3113 in
                                           let t_interp1 =
                                             let a_name =
                                               Prims.strcat "interpretation_"
                                                 tsym in
                                             let uu____3142 =
                                               let uu____3146 =
                                                 let uu____3147 =
                                                   let uu____3153 =
                                                     FStar_SMTEncoding_Util.mkIff
                                                       (f_has_t_z, t_interp) in
                                                   ([[f_has_t_z]], (fsym ::
                                                     cvars), uu____3153) in
                                                 FStar_SMTEncoding_Util.mkForall
                                                   uu____3147 in
                                               (uu____3146, (Some a_name),
                                                 (Prims.strcat module_name
                                                    (Prims.strcat "_" a_name))) in
                                             FStar_SMTEncoding_Util.mkAssume
                                               uu____3142 in
                                           let t_decls =
                                             FStar_List.append (tdecl ::
                                               decls)
                                               (FStar_List.append decls'
                                                  (FStar_List.append
                                                     guard_decls
                                                     [k_assumption;
                                                     pre_typing;
                                                     t_interp1])) in
                                           ((let uu____3167 =
                                               mk_cache_entry env tsym
                                                 cvar_sorts t_decls in
                                             FStar_Util.smap_add env.cache
                                               tkey_hash uu____3167);
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
                     let uu____3178 =
                       let uu____3182 =
                         FStar_SMTEncoding_Term.mk_HasType t1
                           FStar_SMTEncoding_Term.mk_Term_type in
                       (uu____3182, (Some "Typing for non-total arrows"),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3178 in
                   let fsym = ("f", FStar_SMTEncoding_Term.Term_sort) in
                   let f = FStar_SMTEncoding_Util.mkFreeV fsym in
                   let f_has_t = FStar_SMTEncoding_Term.mk_HasType f t1 in
                   let t_interp =
                     let a_name = Prims.strcat "pre_typing_" tsym in
                     let uu____3191 =
                       let uu____3195 =
                         let uu____3196 =
                           let uu____3202 =
                             let uu____3203 =
                               let uu____3206 =
                                 let uu____3207 =
                                   FStar_SMTEncoding_Term.mk_PreType f in
                                 FStar_SMTEncoding_Term.mk_tester "Tm_arrow"
                                   uu____3207 in
                               (f_has_t, uu____3206) in
                             FStar_SMTEncoding_Util.mkImp uu____3203 in
                           ([[f_has_t]], [fsym], uu____3202) in
                         mkForall_fuel uu____3196 in
                       (uu____3195, (Some a_name),
                         (Prims.strcat module_name (Prims.strcat "_" a_name))) in
                     FStar_SMTEncoding_Util.mkAssume uu____3191 in
                   (t1, [tdecl; t_kinding; t_interp])))
       | FStar_Syntax_Syntax.Tm_refine uu____3221 ->
           let uu____3226 =
             let uu____3229 =
               FStar_TypeChecker_Normalize.normalize_refinement
                 [FStar_TypeChecker_Normalize.WHNF;
                 FStar_TypeChecker_Normalize.EraseUniverses] env.tcenv t0 in
             match uu____3229 with
             | { FStar_Syntax_Syntax.n = FStar_Syntax_Syntax.Tm_refine (x,f);
                 FStar_Syntax_Syntax.tk = uu____3234;
                 FStar_Syntax_Syntax.pos = uu____3235;
                 FStar_Syntax_Syntax.vars = uu____3236;_} ->
                 let uu____3243 = FStar_Syntax_Subst.open_term [(x, None)] f in
                 (match uu____3243 with
                  | (b,f1) ->
                      let uu____3257 =
                        let uu____3258 = FStar_List.hd b in fst uu____3258 in
                      (uu____3257, f1))
             | uu____3263 -> failwith "impossible" in
           (match uu____3226 with
            | (x,f) ->
                let uu____3270 = encode_term x.FStar_Syntax_Syntax.sort env in
                (match uu____3270 with
                 | (base_t,decls) ->
                     let uu____3277 = gen_term_var env x in
                     (match uu____3277 with
                      | (x1,xtm,env') ->
                          let uu____3286 = encode_formula f env' in
                          (match uu____3286 with
                           | (refinement,decls') ->
                               let uu____3293 =
                                 fresh_fvar "f"
                                   FStar_SMTEncoding_Term.Fuel_sort in
                               (match uu____3293 with
                                | (fsym,fterm) ->
                                    let tm_has_type_with_fuel =
                                      FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                        (Some fterm) xtm base_t in
                                    let encoding =
                                      FStar_SMTEncoding_Util.mkAnd
                                        (tm_has_type_with_fuel, refinement) in
                                    let cvars =
                                      let uu____3304 =
                                        let uu____3306 =
                                          FStar_SMTEncoding_Term.free_variables
                                            refinement in
                                        let uu____3310 =
                                          FStar_SMTEncoding_Term.free_variables
                                            tm_has_type_with_fuel in
                                        FStar_List.append uu____3306
                                          uu____3310 in
                                      FStar_Util.remove_dups
                                        FStar_SMTEncoding_Term.fv_eq
                                        uu____3304 in
                                    let cvars1 =
                                      FStar_All.pipe_right cvars
                                        (FStar_List.filter
                                           (fun uu____3326  ->
                                              match uu____3326 with
                                              | (y,uu____3330) ->
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
                                    let uu____3349 =
                                      FStar_Util.smap_try_find env.cache
                                        tkey_hash in
                                    (match uu____3349 with
                                     | Some cache_entry ->
                                         let uu____3354 =
                                           let uu____3355 =
                                             let uu____3359 =
                                               FStar_All.pipe_right cvars1
                                                 (FStar_List.map
                                                    FStar_SMTEncoding_Util.mkFreeV) in
                                             ((cache_entry.cache_symbol_name),
                                               uu____3359) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3355 in
                                         (uu____3354,
                                           (FStar_List.append decls
                                              (FStar_List.append decls'
                                                 (use_cache_entry cache_entry))))
                                     | None  ->
                                         let module_name =
                                           env.current_module_name in
                                         let tsym =
                                           let uu____3371 =
                                             let uu____3372 =
                                               let uu____3373 =
                                                 FStar_Util.digest_of_string
                                                   tkey_hash in
                                               Prims.strcat "_Tm_refine_"
                                                 uu____3373 in
                                             Prims.strcat module_name
                                               uu____3372 in
                                           varops.mk_unique uu____3371 in
                                         let cvar_sorts =
                                           FStar_List.map
                                             FStar_Pervasives.snd cvars1 in
                                         let tdecl =
                                           FStar_SMTEncoding_Term.DeclFun
                                             (tsym, cvar_sorts,
                                               FStar_SMTEncoding_Term.Term_sort,
                                               None) in
                                         let t1 =
                                           let uu____3382 =
                                             let uu____3386 =
                                               FStar_List.map
                                                 FStar_SMTEncoding_Util.mkFreeV
                                                 cvars1 in
                                             (tsym, uu____3386) in
                                           FStar_SMTEncoding_Util.mkApp
                                             uu____3382 in
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
                                           let uu____3396 =
                                             let uu____3400 =
                                               let uu____3401 =
                                                 let uu____3407 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (t_haseq_ref,
                                                       t_haseq_base) in
                                                 ([[t_haseq_ref]], cvars1,
                                                   uu____3407) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3401 in
                                             (uu____3400,
                                               (Some
                                                  (Prims.strcat "haseq for "
                                                     tsym)),
                                               (Prims.strcat "haseq" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3396 in
                                         let t_kinding =
                                           let uu____3417 =
                                             let uu____3421 =
                                               FStar_SMTEncoding_Util.mkForall
                                                 ([[t_has_kind]], cvars1,
                                                   t_has_kind) in
                                             (uu____3421,
                                               (Some "refinement kinding"),
                                               (Prims.strcat
                                                  "refinement_kinding_" tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3417 in
                                         let t_interp =
                                           let uu____3431 =
                                             let uu____3435 =
                                               let uu____3436 =
                                                 let uu____3442 =
                                                   FStar_SMTEncoding_Util.mkIff
                                                     (x_has_t, encoding) in
                                                 ([[x_has_t]], (ffv :: xfv ::
                                                   cvars1), uu____3442) in
                                               FStar_SMTEncoding_Util.mkForall
                                                 uu____3436 in
                                             let uu____3454 =
                                               let uu____3456 =
                                                 FStar_Syntax_Print.term_to_string
                                                   t0 in
                                               Some uu____3456 in
                                             (uu____3435, uu____3454,
                                               (Prims.strcat
                                                  "refinement_interpretation_"
                                                  tsym)) in
                                           FStar_SMTEncoding_Util.mkAssume
                                             uu____3431 in
                                         let t_decls =
                                           FStar_List.append decls
                                             (FStar_List.append decls'
                                                [tdecl;
                                                t_kinding;
                                                t_interp;
                                                t_haseq1]) in
                                         ((let uu____3461 =
                                             mk_cache_entry env tsym
                                               cvar_sorts t_decls in
                                           FStar_Util.smap_add env.cache
                                             tkey_hash uu____3461);
                                          (t1, t_decls))))))))
       | FStar_Syntax_Syntax.Tm_uvar (uv,k) ->
           let ttm =
             let uu____3482 = FStar_Syntax_Unionfind.uvar_id uv in
             FStar_SMTEncoding_Util.mk_Term_uvar uu____3482 in
           let uu____3483 = encode_term_pred None k env ttm in
           (match uu____3483 with
            | (t_has_k,decls) ->
                let d =
                  let uu____3491 =
                    let uu____3495 =
                      let uu____3496 =
                        let uu____3497 =
                          let uu____3498 = FStar_Syntax_Unionfind.uvar_id uv in
                          FStar_All.pipe_left FStar_Util.string_of_int
                            uu____3498 in
                        FStar_Util.format1 "uvar_typing_%s" uu____3497 in
                      varops.mk_unique uu____3496 in
                    (t_has_k, (Some "Uvar typing"), uu____3495) in
                  FStar_SMTEncoding_Util.mkAssume uu____3491 in
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
                       FStar_Syntax_Const.lexcons_lid
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
                       FStar_Syntax_Const.lexcons_lid
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
                         uu____3721 None t0.FStar_Syntax_Syntax.pos in
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
                                 | None  ->
                                     (app_tm,
                                       (FStar_List.append decls decls'))
                                 | Some (formals,c) ->
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
                                            encode_term_pred None ty env
                                              app_tm in
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
                                                     (Some
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
                                -> Some (x.FStar_Syntax_Syntax.sort)
                            | FStar_Syntax_Syntax.Tm_name x ->
                                Some (x.FStar_Syntax_Syntax.sort)
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
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____3995
                                    FStar_Pervasives.snd in
                                Some uu____3994
                            | FStar_Syntax_Syntax.Tm_fvar fv ->
                                let uu____4018 =
                                  let uu____4019 =
                                    let uu____4022 =
                                      FStar_TypeChecker_Env.lookup_lid
                                        env.tcenv
                                        (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                    FStar_All.pipe_right uu____4022
                                      FStar_Pervasives.fst in
                                  FStar_All.pipe_right uu____4019
                                    FStar_Pervasives.snd in
                                Some uu____4018
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4041,(FStar_Util.Inl t1,uu____4043),uu____4044)
                                -> Some t1
                            | FStar_Syntax_Syntax.Tm_ascribed
                                (uu____4082,(FStar_Util.Inr c,uu____4084),uu____4085)
                                -> Some (FStar_Syntax_Util.comp_result c)
                            | uu____4123 -> None in
                          (match head_type with
                           | None  -> encode_partial_app None
                           | Some head_type1 ->
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
                                             (Some (formals, c))
                                         else encode_partial_app None))))))
       | FStar_Syntax_Syntax.Tm_abs (bs,body,lopt) ->
           let uu____4226 = FStar_Syntax_Subst.open_term' bs body in
           (match uu____4226 with
            | (bs1,body1,opening) ->
                let fallback uu____4241 =
                  let f = varops.fresh "Tm_abs" in
                  let decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (f, [], FStar_SMTEncoding_Term.Term_sort,
                        (Some "Imprecise function encoding")) in
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
                        (fun _0_31  -> Some _0_31)
                  | FStar_Util.Inr (eff,flags) ->
                      let new_uvar1 uu____4364 =
                        let uu____4365 =
                          FStar_TypeChecker_Rel.new_uvar
                            FStar_Range.dummyRange []
                            FStar_Syntax_Util.ktype0 in
                        FStar_All.pipe_right uu____4365 FStar_Pervasives.fst in
                      if
                        FStar_Ident.lid_equals eff
                          FStar_Syntax_Const.effect_Tot_lid
                      then
                        let uu____4373 =
                          let uu____4374 = new_uvar1 () in
                          FStar_Syntax_Syntax.mk_Total uu____4374 in
                        FStar_All.pipe_right uu____4373
                          (fun _0_32  -> Some _0_32)
                      else
                        if
                          FStar_Ident.lid_equals eff
                            FStar_Syntax_Const.effect_GTot_lid
                        then
                          (let uu____4378 =
                             let uu____4379 = new_uvar1 () in
                             FStar_Syntax_Syntax.mk_GTotal uu____4379 in
                           FStar_All.pipe_right uu____4378
                             (fun _0_33  -> Some _0_33))
                        else None in
                (match lopt with
                 | None  ->
                     ((let uu____4390 =
                         let uu____4391 =
                           FStar_Syntax_Print.term_to_string t0 in
                         FStar_Util.format1
                           "Losing precision when encoding a function literal: %s\n(Unnannotated abstraction in the compiler ?)"
                           uu____4391 in
                       FStar_Errors.warn t0.FStar_Syntax_Syntax.pos
                         uu____4390);
                      fallback ())
                 | Some lc ->
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
                        let uu____4412 = encode_binders None bs1 env in
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
                                        | None  -> (None, [])
                                        | Some c ->
                                            let tfun =
                                              FStar_Syntax_Util.arrow bs1 c in
                                            let uu____4491 =
                                              encode_term tfun env in
                                            (match uu____4491 with
                                             | (t1,decls1) ->
                                                 ((Some t1), decls1)) in
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
                                             | None  -> cvars
                                             | Some t1 ->
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
                                            | Some cache_entry ->
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
                                            | None  ->
                                                let uu____4557 =
                                                  is_an_eta_expansion env
                                                    vars body3 in
                                                (match uu____4557 with
                                                 | Some t1 ->
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
                                                 | None  ->
                                                     let cvar_sorts =
                                                       FStar_List.map
                                                         FStar_Pervasives.snd
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
                                                           None) in
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
                                                       | None  -> []
                                                       | Some t1 ->
                                                           let f_has_t =
                                                             FStar_SMTEncoding_Term.mk_HasTypeWithFuel
                                                               None f t1 in
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
                                                                 (Some a_name),
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
                                                           (Some a_name),
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
                 (e, [], FStar_SMTEncoding_Term.Term_sort, None) in
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
              let uu____4732 = encode_term e1 env in
              match uu____4732 with
              | (ee1,decls1) ->
                  let uu____4739 =
                    FStar_Syntax_Subst.open_term [(x, None)] e2 in
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
               (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t))
            -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun e  ->
    fun pats  ->
      fun default_case  ->
        fun env  ->
          fun encode_br  ->
            let uu____4785 =
              let uu____4789 =
                let uu____4790 =
                  FStar_Syntax_Syntax.mk FStar_Syntax_Syntax.Tm_unknown None
                    FStar_Range.dummyRange in
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
                                         | None  -> (guard, [])
                                         | Some w1 ->
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
and encode_pat: env_t -> FStar_Syntax_Syntax.pat -> (env_t* pattern) =
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
      (FStar_SMTEncoding_Term.term Prims.list*
        FStar_SMTEncoding_Term.decls_t)
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
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun t  ->
    fun env  ->
      let list_elements1 e =
        let uu____5356 = FStar_Syntax_Util.list_elements e in
        match uu____5356 with
        | Some l -> l
        | None  ->
            (FStar_Errors.warn e.FStar_Syntax_Syntax.pos
               "SMT pattern is not a list literal; ignoring the pattern";
             []) in
      let one_pat p =
        let uu____5374 =
          let uu____5384 = FStar_Syntax_Util.unmeta p in
          FStar_All.pipe_right uu____5384 FStar_Syntax_Util.head_and_args in
        match uu____5374 with
        | (head1,args) ->
            let uu____5415 =
              let uu____5423 =
                let uu____5424 = FStar_Syntax_Util.un_uinst head1 in
                uu____5424.FStar_Syntax_Syntax.n in
              (uu____5423, args) in
            (match uu____5415 with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(uu____5438,uu____5439)::(e,uu____5441)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpat_lid
                 -> (e, None)
             | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5472)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.smtpatT_lid
                 -> (e, None)
             | uu____5493 -> failwith "Unexpected pattern term") in
      let lemma_pats p =
        let elts = list_elements1 p in
        let smt_pat_or t1 =
          let uu____5526 =
            let uu____5536 = FStar_Syntax_Util.unmeta t1 in
            FStar_All.pipe_right uu____5536 FStar_Syntax_Util.head_and_args in
          match uu____5526 with
          | (head1,args) ->
              let uu____5565 =
                let uu____5573 =
                  let uu____5574 = FStar_Syntax_Util.un_uinst head1 in
                  uu____5574.FStar_Syntax_Syntax.n in
                (uu____5573, args) in
              (match uu____5565 with
               | (FStar_Syntax_Syntax.Tm_fvar fv,(e,uu____5587)::[]) when
                   FStar_Syntax_Syntax.fv_eq_lid fv
                     FStar_Syntax_Const.smtpatOr_lid
                   -> Some e
               | uu____5607 -> None) in
        match elts with
        | t1::[] ->
            let uu____5625 = smt_pat_or t1 in
            (match uu____5625 with
             | Some e ->
                 let uu____5641 = list_elements1 e in
                 FStar_All.pipe_right uu____5641
                   (FStar_List.map
                      (fun branch1  ->
                         let uu____5658 = list_elements1 branch1 in
                         FStar_All.pipe_right uu____5658
                           (FStar_List.map one_pat)))
             | uu____5672 ->
                 let uu____5676 =
                   FStar_All.pipe_right elts (FStar_List.map one_pat) in
                 [uu____5676])
        | uu____5707 ->
            let uu____5709 =
              FStar_All.pipe_right elts (FStar_List.map one_pat) in
            [uu____5709] in
      let uu____5740 =
        let uu____5756 =
          let uu____5757 = FStar_Syntax_Subst.compress t in
          uu____5757.FStar_Syntax_Syntax.n in
        match uu____5756 with
        | FStar_Syntax_Syntax.Tm_arrow (binders,c) ->
            let uu____5787 = FStar_Syntax_Subst.open_comp binders c in
            (match uu____5787 with
             | (binders1,c1) ->
                 (match c1.FStar_Syntax_Syntax.n with
                  | FStar_Syntax_Syntax.Comp
                      { FStar_Syntax_Syntax.comp_univs = uu____5822;
                        FStar_Syntax_Syntax.effect_name = uu____5823;
                        FStar_Syntax_Syntax.result_typ = uu____5824;
                        FStar_Syntax_Syntax.effect_args =
                          (pre,uu____5826)::(post,uu____5828)::(pats,uu____5830)::[];
                        FStar_Syntax_Syntax.flags = uu____5831;_}
                      ->
                      let uu____5863 = lemma_pats pats in
                      (binders1, pre, post, uu____5863)
                  | uu____5882 -> failwith "impos"))
        | uu____5898 -> failwith "Impos" in
      match uu____5740 with
      | (binders,pre,post,patterns) ->
          let env1 =
            let uu___137_5943 = env in
            {
              bindings = (uu___137_5943.bindings);
              depth = (uu___137_5943.depth);
              tcenv = (uu___137_5943.tcenv);
              warn = (uu___137_5943.warn);
              cache = (uu___137_5943.cache);
              nolabels = (uu___137_5943.nolabels);
              use_zfuel_name = true;
              encode_non_total_function_typ =
                (uu___137_5943.encode_non_total_function_typ);
              current_module_name = (uu___137_5943.current_module_name)
            } in
          let uu____5944 = encode_binders None binders env1 in
          (match uu____5944 with
           | (vars,guards,env2,decls,uu____5959) ->
               let uu____5966 =
                 let uu____5973 =
                   FStar_All.pipe_right patterns
                     (FStar_List.map
                        (fun branch1  ->
                           let uu____6004 =
                             let uu____6009 =
                               FStar_All.pipe_right branch1
                                 (FStar_List.map
                                    (fun uu____6025  ->
                                       match uu____6025 with
                                       | (t1,uu____6032) ->
                                           encode_term t1 env2)) in
                             FStar_All.pipe_right uu____6009 FStar_List.unzip in
                           match uu____6004 with
                           | (pats,decls1) -> (pats, decls1))) in
                 FStar_All.pipe_right uu____5973 FStar_List.unzip in
               (match uu____5966 with
                | (pats,decls') ->
                    let decls'1 = FStar_List.flatten decls' in
                    let env3 =
                      let uu___138_6082 = env2 in
                      {
                        bindings = (uu___138_6082.bindings);
                        depth = (uu___138_6082.depth);
                        tcenv = (uu___138_6082.tcenv);
                        warn = (uu___138_6082.warn);
                        cache = (uu___138_6082.cache);
                        nolabels = true;
                        use_zfuel_name = (uu___138_6082.use_zfuel_name);
                        encode_non_total_function_typ =
                          (uu___138_6082.encode_non_total_function_typ);
                        current_module_name =
                          (uu___138_6082.current_module_name)
                      } in
                    let uu____6083 =
                      let uu____6086 = FStar_Syntax_Util.unmeta pre in
                      encode_formula uu____6086 env3 in
                    (match uu____6083 with
                     | (pre1,decls'') ->
                         let uu____6091 =
                           let uu____6094 = FStar_Syntax_Util.unmeta post in
                           encode_formula uu____6094 env3 in
                         (match uu____6091 with
                          | (post1,decls''') ->
                              let decls1 =
                                FStar_List.append decls
                                  (FStar_List.append
                                     (FStar_List.flatten decls'1)
                                     (FStar_List.append decls'' decls''')) in
                              let uu____6101 =
                                let uu____6102 =
                                  let uu____6108 =
                                    let uu____6109 =
                                      let uu____6112 =
                                        FStar_SMTEncoding_Util.mk_and_l (pre1
                                          :: guards) in
                                      (uu____6112, post1) in
                                    FStar_SMTEncoding_Util.mkImp uu____6109 in
                                  (pats, vars, uu____6108) in
                                FStar_SMTEncoding_Util.mkForall uu____6102 in
                              (uu____6101, decls1)))))
and encode_formula:
  FStar_Syntax_Syntax.typ ->
    env_t -> (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decls_t)
  =
  fun phi  ->
    fun env  ->
      let debug1 phi1 =
        let uu____6125 =
          FStar_All.pipe_left (FStar_TypeChecker_Env.debug env.tcenv)
            (FStar_Options.Other "SMTEncoding") in
        if uu____6125
        then
          let uu____6126 = FStar_Syntax_Print.tag_of_term phi1 in
          let uu____6127 = FStar_Syntax_Print.term_to_string phi1 in
          FStar_Util.print2 "Formula (%s)  %s\n" uu____6126 uu____6127
        else () in
      let enc f r l =
        let uu____6154 =
          FStar_Util.fold_map
            (fun decls  ->
               fun x  ->
                 let uu____6167 = encode_term (fst x) env in
                 match uu____6167 with
                 | (t,decls') -> ((FStar_List.append decls decls'), t)) [] l in
        match uu____6154 with
        | (decls,args) ->
            let uu____6184 =
              let uu___139_6185 = f args in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___139_6185.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___139_6185.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6184, decls) in
      let const_op f r uu____6204 = let uu____6207 = f r in (uu____6207, []) in
      let un_op f l =
        let uu____6223 = FStar_List.hd l in FStar_All.pipe_left f uu____6223 in
      let bin_op f uu___111_6236 =
        match uu___111_6236 with
        | t1::t2::[] -> f (t1, t2)
        | uu____6244 -> failwith "Impossible" in
      let enc_prop_c f r l =
        let uu____6271 =
          FStar_Util.fold_map
            (fun decls  ->
               fun uu____6280  ->
                 match uu____6280 with
                 | (t,uu____6288) ->
                     let uu____6289 = encode_formula t env in
                     (match uu____6289 with
                      | (phi1,decls') ->
                          ((FStar_List.append decls decls'), phi1))) [] l in
        match uu____6271 with
        | (decls,phis) ->
            let uu____6306 =
              let uu___140_6307 = f phis in
              {
                FStar_SMTEncoding_Term.tm =
                  (uu___140_6307.FStar_SMTEncoding_Term.tm);
                FStar_SMTEncoding_Term.freevars =
                  (uu___140_6307.FStar_SMTEncoding_Term.freevars);
                FStar_SMTEncoding_Term.rng = r
              } in
            (uu____6306, decls) in
      let eq_op r uu___112_6323 =
        match uu___112_6323 with
        | uu____6326::e1::e2::[] ->
            let uu____6357 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6357 r [e1; e2]
        | uu____6376::uu____6377::e1::e2::[] ->
            let uu____6416 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6416 r [e1; e2]
        | l ->
            let uu____6436 = enc (bin_op FStar_SMTEncoding_Util.mkEq) in
            uu____6436 r l in
      let mk_imp1 r uu___113_6455 =
        match uu___113_6455 with
        | (lhs,uu____6459)::(rhs,uu____6461)::[] ->
            let uu____6482 = encode_formula rhs env in
            (match uu____6482 with
             | (l1,decls1) ->
                 (match l1.FStar_SMTEncoding_Term.tm with
                  | FStar_SMTEncoding_Term.App
                      (FStar_SMTEncoding_Term.TrueOp ,uu____6491) ->
                      (l1, decls1)
                  | uu____6494 ->
                      let uu____6495 = encode_formula lhs env in
                      (match uu____6495 with
                       | (l2,decls2) ->
                           let uu____6502 =
                             FStar_SMTEncoding_Term.mkImp (l2, l1) r in
                           (uu____6502, (FStar_List.append decls1 decls2)))))
        | uu____6504 -> failwith "impossible" in
      let mk_ite r uu___114_6519 =
        match uu___114_6519 with
        | (guard,uu____6523)::(_then,uu____6525)::(_else,uu____6527)::[] ->
            let uu____6556 = encode_formula guard env in
            (match uu____6556 with
             | (g,decls1) ->
                 let uu____6563 = encode_formula _then env in
                 (match uu____6563 with
                  | (t,decls2) ->
                      let uu____6570 = encode_formula _else env in
                      (match uu____6570 with
                       | (e,decls3) ->
                           let res = FStar_SMTEncoding_Term.mkITE (g, t, e) r in
                           (res,
                             (FStar_List.append decls1
                                (FStar_List.append decls2 decls3))))))
        | uu____6579 -> failwith "impossible" in
      let unboxInt_l f l =
        let uu____6598 = FStar_List.map FStar_SMTEncoding_Term.unboxInt l in
        f uu____6598 in
      let connectives =
        let uu____6610 =
          let uu____6619 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkAnd) in
          (FStar_Syntax_Const.and_lid, uu____6619) in
        let uu____6632 =
          let uu____6642 =
            let uu____6651 = enc_prop_c (bin_op FStar_SMTEncoding_Util.mkOr) in
            (FStar_Syntax_Const.or_lid, uu____6651) in
          let uu____6664 =
            let uu____6674 =
              let uu____6684 =
                let uu____6693 =
                  enc_prop_c (bin_op FStar_SMTEncoding_Util.mkIff) in
                (FStar_Syntax_Const.iff_lid, uu____6693) in
              let uu____6706 =
                let uu____6716 =
                  let uu____6726 =
                    let uu____6735 =
                      enc_prop_c (un_op FStar_SMTEncoding_Util.mkNot) in
                    (FStar_Syntax_Const.not_lid, uu____6735) in
                  [uu____6726;
                  (FStar_Syntax_Const.eq2_lid, eq_op);
                  (FStar_Syntax_Const.eq3_lid, eq_op);
                  (FStar_Syntax_Const.true_lid,
                    (const_op FStar_SMTEncoding_Term.mkTrue));
                  (FStar_Syntax_Const.false_lid,
                    (const_op FStar_SMTEncoding_Term.mkFalse))] in
                (FStar_Syntax_Const.ite_lid, mk_ite) :: uu____6716 in
              uu____6684 :: uu____6706 in
            (FStar_Syntax_Const.imp_lid, mk_imp1) :: uu____6674 in
          uu____6642 :: uu____6664 in
        uu____6610 :: uu____6632 in
      let rec fallback phi1 =
        match phi1.FStar_Syntax_Syntax.n with
        | FStar_Syntax_Syntax.Tm_meta
            (phi',FStar_Syntax_Syntax.Meta_labeled (msg,r,b)) ->
            let uu____6897 = encode_formula phi' env in
            (match uu____6897 with
             | (phi2,decls) ->
                 let uu____6904 =
                   FStar_SMTEncoding_Term.mk
                     (FStar_SMTEncoding_Term.Labeled (phi2, msg, r)) r in
                 (uu____6904, decls))
        | FStar_Syntax_Syntax.Tm_meta uu____6905 ->
            let uu____6910 = FStar_Syntax_Util.unmeta phi1 in
            encode_formula uu____6910 env
        | FStar_Syntax_Syntax.Tm_match (e,pats) ->
            let uu____6939 =
              encode_match e pats FStar_SMTEncoding_Util.mkFalse env
                encode_formula in
            (match uu____6939 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_let
            ((false
              ,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inl x;
                 FStar_Syntax_Syntax.lbunivs = uu____6947;
                 FStar_Syntax_Syntax.lbtyp = t1;
                 FStar_Syntax_Syntax.lbeff = uu____6949;
                 FStar_Syntax_Syntax.lbdef = e1;_}::[]),e2)
            ->
            let uu____6965 = encode_let x t1 e1 e2 env encode_formula in
            (match uu____6965 with | (t,decls) -> (t, decls))
        | FStar_Syntax_Syntax.Tm_app (head1,args) ->
            let head2 = FStar_Syntax_Util.un_uinst head1 in
            (match ((head2.FStar_Syntax_Syntax.n), args) with
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,uu____6997::(x,uu____6999)::(t,uu____7001)::[]) when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.has_type_lid
                 ->
                 let uu____7035 = encode_term x env in
                 (match uu____7035 with
                  | (x1,decls) ->
                      let uu____7042 = encode_term t env in
                      (match uu____7042 with
                       | (t1,decls') ->
                           let uu____7049 =
                             FStar_SMTEncoding_Term.mk_HasType x1 t1 in
                           (uu____7049, (FStar_List.append decls decls'))))
             | (FStar_Syntax_Syntax.Tm_fvar
                fv,(r,uu____7053)::(msg,uu____7055)::(phi2,uu____7057)::[])
                 when
                 FStar_Syntax_Syntax.fv_eq_lid fv
                   FStar_Syntax_Const.labeled_lid
                 ->
                 let uu____7091 =
                   let uu____7094 =
                     let uu____7095 = FStar_Syntax_Subst.compress r in
                     uu____7095.FStar_Syntax_Syntax.n in
                   let uu____7098 =
                     let uu____7099 = FStar_Syntax_Subst.compress msg in
                     uu____7099.FStar_Syntax_Syntax.n in
                   (uu____7094, uu____7098) in
                 (match uu____7091 with
                  | (FStar_Syntax_Syntax.Tm_constant (FStar_Const.Const_range
                     r1),FStar_Syntax_Syntax.Tm_constant
                     (FStar_Const.Const_string (s,uu____7106))) ->
                      let phi3 =
                        (FStar_Syntax_Syntax.mk
                           (FStar_Syntax_Syntax.Tm_meta
                              (phi2,
                                (FStar_Syntax_Syntax.Meta_labeled
                                   ((FStar_Util.string_of_unicode s), r1,
                                     false))))) None r1 in
                      fallback phi3
                  | uu____7122 -> fallback phi2)
             | uu____7125 when head_redex env head2 ->
                 let uu____7133 = whnf env phi1 in
                 encode_formula uu____7133 env
             | uu____7134 ->
                 let uu____7142 = encode_term phi1 env in
                 (match uu____7142 with
                  | (tt,decls) ->
                      let uu____7149 =
                        FStar_SMTEncoding_Term.mk_Valid
                          (let uu___141_7150 = tt in
                           {
                             FStar_SMTEncoding_Term.tm =
                               (uu___141_7150.FStar_SMTEncoding_Term.tm);
                             FStar_SMTEncoding_Term.freevars =
                               (uu___141_7150.FStar_SMTEncoding_Term.freevars);
                             FStar_SMTEncoding_Term.rng =
                               (phi1.FStar_Syntax_Syntax.pos)
                           }) in
                      (uu____7149, decls)))
        | uu____7153 ->
            let uu____7154 = encode_term phi1 env in
            (match uu____7154 with
             | (tt,decls) ->
                 let uu____7161 =
                   FStar_SMTEncoding_Term.mk_Valid
                     (let uu___142_7162 = tt in
                      {
                        FStar_SMTEncoding_Term.tm =
                          (uu___142_7162.FStar_SMTEncoding_Term.tm);
                        FStar_SMTEncoding_Term.freevars =
                          (uu___142_7162.FStar_SMTEncoding_Term.freevars);
                        FStar_SMTEncoding_Term.rng =
                          (phi1.FStar_Syntax_Syntax.pos)
                      }) in
                 (uu____7161, decls)) in
      let encode_q_body env1 bs ps body =
        let uu____7189 = encode_binders None bs env1 in
        match uu____7189 with
        | (vars,guards,env2,decls,uu____7211) ->
            let uu____7218 =
              let uu____7225 =
                FStar_All.pipe_right ps
                  (FStar_List.map
                     (fun p  ->
                        let uu____7248 =
                          let uu____7253 =
                            FStar_All.pipe_right p
                              (FStar_List.map
                                 (fun uu____7267  ->
                                    match uu____7267 with
                                    | (t,uu____7273) ->
                                        encode_term t
                                          (let uu___143_7274 = env2 in
                                           {
                                             bindings =
                                               (uu___143_7274.bindings);
                                             depth = (uu___143_7274.depth);
                                             tcenv = (uu___143_7274.tcenv);
                                             warn = (uu___143_7274.warn);
                                             cache = (uu___143_7274.cache);
                                             nolabels =
                                               (uu___143_7274.nolabels);
                                             use_zfuel_name = true;
                                             encode_non_total_function_typ =
                                               (uu___143_7274.encode_non_total_function_typ);
                                             current_module_name =
                                               (uu___143_7274.current_module_name)
                                           }))) in
                          FStar_All.pipe_right uu____7253 FStar_List.unzip in
                        match uu____7248 with
                        | (p1,decls1) -> (p1, (FStar_List.flatten decls1)))) in
              FStar_All.pipe_right uu____7225 FStar_List.unzip in
            (match uu____7218 with
             | (pats,decls') ->
                 let uu____7326 = encode_formula body env2 in
                 (match uu____7326 with
                  | (body1,decls'') ->
                      let guards1 =
                        match pats with
                        | ({
                             FStar_SMTEncoding_Term.tm =
                               FStar_SMTEncoding_Term.App
                               (FStar_SMTEncoding_Term.Var gf,p::[]);
                             FStar_SMTEncoding_Term.freevars = uu____7345;
                             FStar_SMTEncoding_Term.rng = uu____7346;_}::[])::[]
                            when
                            (FStar_Ident.text_of_lid
                               FStar_Syntax_Const.guard_free)
                              = gf
                            -> []
                        | uu____7354 -> guards in
                      let uu____7357 =
                        FStar_SMTEncoding_Util.mk_and_l guards1 in
                      (vars, pats, uu____7357, body1,
                        (FStar_List.append decls
                           (FStar_List.append (FStar_List.flatten decls')
                              decls''))))) in
      debug1 phi;
      (let phi1 = FStar_Syntax_Util.unascribe phi in
       let check_pattern_vars vars pats =
         let pats1 =
           FStar_All.pipe_right pats
             (FStar_List.map
                (fun uu____7391  ->
                   match uu____7391 with
                   | (x,uu____7395) ->
                       FStar_TypeChecker_Normalize.normalize
                         [FStar_TypeChecker_Normalize.Beta;
                         FStar_TypeChecker_Normalize.AllowUnboundUniverses;
                         FStar_TypeChecker_Normalize.EraseUniverses]
                         env.tcenv x)) in
         match pats1 with
         | [] -> ()
         | hd1::tl1 ->
             let pat_vars =
               let uu____7401 = FStar_Syntax_Free.names hd1 in
               FStar_List.fold_left
                 (fun out  ->
                    fun x  ->
                      let uu____7407 = FStar_Syntax_Free.names x in
                      FStar_Util.set_union out uu____7407) uu____7401 tl1 in
             let uu____7409 =
               FStar_All.pipe_right vars
                 (FStar_Util.find_opt
                    (fun uu____7421  ->
                       match uu____7421 with
                       | (b,uu____7425) ->
                           let uu____7426 = FStar_Util.set_mem b pat_vars in
                           Prims.op_Negation uu____7426)) in
             (match uu____7409 with
              | None  -> ()
              | Some (x,uu____7430) ->
                  let pos =
                    FStar_List.fold_left
                      (fun out  ->
                         fun t  ->
                           FStar_Range.union_ranges out
                             t.FStar_Syntax_Syntax.pos)
                      hd1.FStar_Syntax_Syntax.pos tl1 in
                  let uu____7440 =
                    let uu____7441 = FStar_Syntax_Print.bv_to_string x in
                    FStar_Util.format1
                      "SMT pattern misses at least one bound variable: %s"
                      uu____7441 in
                  FStar_Errors.warn pos uu____7440) in
       let uu____7442 = FStar_Syntax_Util.destruct_typ_as_formula phi1 in
       match uu____7442 with
       | None  -> fallback phi1
       | Some (FStar_Syntax_Util.BaseConn (op,arms)) ->
           let uu____7448 =
             FStar_All.pipe_right connectives
               (FStar_List.tryFind
                  (fun uu____7484  ->
                     match uu____7484 with
                     | (l,uu____7494) -> FStar_Ident.lid_equals op l)) in
           (match uu____7448 with
            | None  -> fallback phi1
            | Some (uu____7517,f) -> f phi1.FStar_Syntax_Syntax.pos arms)
       | Some (FStar_Syntax_Util.QAll (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7546 = encode_q_body env vars pats body in
             match uu____7546 with
             | (vars1,pats1,guard,body1,decls) ->
                 let tm =
                   let uu____7572 =
                     let uu____7578 =
                       FStar_SMTEncoding_Util.mkImp (guard, body1) in
                     (pats1, vars1, uu____7578) in
                   FStar_SMTEncoding_Term.mkForall uu____7572
                     phi1.FStar_Syntax_Syntax.pos in
                 (tm, decls)))
       | Some (FStar_Syntax_Util.QEx (vars,pats,body)) ->
           (FStar_All.pipe_right pats
              (FStar_List.iter (check_pattern_vars vars));
            (let uu____7590 = encode_q_body env vars pats body in
             match uu____7590 with
             | (vars1,pats1,guard,body1,decls) ->
                 let uu____7615 =
                   let uu____7616 =
                     let uu____7622 =
                       FStar_SMTEncoding_Util.mkAnd (guard, body1) in
                     (pats1, vars1, uu____7622) in
                   FStar_SMTEncoding_Term.mkExists uu____7616
                     phi1.FStar_Syntax_Syntax.pos in
                 (uu____7615, decls))))
type prims_t =
  {
  mk:
    FStar_Ident.lident ->
      Prims.string ->
        (FStar_SMTEncoding_Term.term* FStar_SMTEncoding_Term.decl Prims.list);
  is: FStar_Ident.lident -> Prims.bool;}
let prims: prims_t =
  let uu____7671 = fresh_fvar "a" FStar_SMTEncoding_Term.Term_sort in
  match uu____7671 with
  | (asym,a) ->
      let uu____7676 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
      (match uu____7676 with
       | (xsym,x) ->
           let uu____7681 = fresh_fvar "y" FStar_SMTEncoding_Term.Term_sort in
           (match uu____7681 with
            | (ysym,y) ->
                let quant vars body x1 =
                  let xname_decl =
                    let uu____7711 =
                      let uu____7717 =
                        FStar_All.pipe_right vars
                          (FStar_List.map FStar_Pervasives.snd) in
                      (x1, uu____7717, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____7711 in
                  let xtok = Prims.strcat x1 "@tok" in
                  let xtok_decl =
                    FStar_SMTEncoding_Term.DeclFun
                      (xtok, [], FStar_SMTEncoding_Term.Term_sort, None) in
                  let xapp =
                    let uu____7732 =
                      let uu____7736 =
                        FStar_List.map FStar_SMTEncoding_Util.mkFreeV vars in
                      (x1, uu____7736) in
                    FStar_SMTEncoding_Util.mkApp uu____7732 in
                  let xtok1 = FStar_SMTEncoding_Util.mkApp (xtok, []) in
                  let xtok_app = mk_Apply xtok1 vars in
                  let uu____7744 =
                    let uu____7746 =
                      let uu____7748 =
                        let uu____7750 =
                          let uu____7751 =
                            let uu____7755 =
                              let uu____7756 =
                                let uu____7762 =
                                  FStar_SMTEncoding_Util.mkEq (xapp, body) in
                                ([[xapp]], vars, uu____7762) in
                              FStar_SMTEncoding_Util.mkForall uu____7756 in
                            (uu____7755, None,
                              (Prims.strcat "primitive_" x1)) in
                          FStar_SMTEncoding_Util.mkAssume uu____7751 in
                        let uu____7771 =
                          let uu____7773 =
                            let uu____7774 =
                              let uu____7778 =
                                let uu____7779 =
                                  let uu____7785 =
                                    FStar_SMTEncoding_Util.mkEq
                                      (xtok_app, xapp) in
                                  ([[xtok_app]], vars, uu____7785) in
                                FStar_SMTEncoding_Util.mkForall uu____7779 in
                              (uu____7778,
                                (Some "Name-token correspondence"),
                                (Prims.strcat "token_correspondence_" x1)) in
                            FStar_SMTEncoding_Util.mkAssume uu____7774 in
                          [uu____7773] in
                        uu____7750 :: uu____7771 in
                      xtok_decl :: uu____7748 in
                    xname_decl :: uu____7746 in
                  (xtok1, uu____7744) in
                let axy =
                  [(asym, FStar_SMTEncoding_Term.Term_sort);
                  (xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let xy =
                  [(xsym, FStar_SMTEncoding_Term.Term_sort);
                  (ysym, FStar_SMTEncoding_Term.Term_sort)] in
                let qx = [(xsym, FStar_SMTEncoding_Term.Term_sort)] in
                let prims1 =
                  let uu____7834 =
                    let uu____7842 =
                      let uu____7848 =
                        let uu____7849 = FStar_SMTEncoding_Util.mkEq (x, y) in
                        FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                          uu____7849 in
                      quant axy uu____7848 in
                    (FStar_Syntax_Const.op_Eq, uu____7842) in
                  let uu____7855 =
                    let uu____7864 =
                      let uu____7872 =
                        let uu____7878 =
                          let uu____7879 =
                            let uu____7880 =
                              FStar_SMTEncoding_Util.mkEq (x, y) in
                            FStar_SMTEncoding_Util.mkNot uu____7880 in
                          FStar_All.pipe_left FStar_SMTEncoding_Term.boxBool
                            uu____7879 in
                        quant axy uu____7878 in
                      (FStar_Syntax_Const.op_notEq, uu____7872) in
                    let uu____7886 =
                      let uu____7895 =
                        let uu____7903 =
                          let uu____7909 =
                            let uu____7910 =
                              let uu____7911 =
                                let uu____7914 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____7915 =
                                  FStar_SMTEncoding_Term.unboxInt y in
                                (uu____7914, uu____7915) in
                              FStar_SMTEncoding_Util.mkLT uu____7911 in
                            FStar_All.pipe_left
                              FStar_SMTEncoding_Term.boxBool uu____7910 in
                          quant xy uu____7909 in
                        (FStar_Syntax_Const.op_LT, uu____7903) in
                      let uu____7921 =
                        let uu____7930 =
                          let uu____7938 =
                            let uu____7944 =
                              let uu____7945 =
                                let uu____7946 =
                                  let uu____7949 =
                                    FStar_SMTEncoding_Term.unboxInt x in
                                  let uu____7950 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  (uu____7949, uu____7950) in
                                FStar_SMTEncoding_Util.mkLTE uu____7946 in
                              FStar_All.pipe_left
                                FStar_SMTEncoding_Term.boxBool uu____7945 in
                            quant xy uu____7944 in
                          (FStar_Syntax_Const.op_LTE, uu____7938) in
                        let uu____7956 =
                          let uu____7965 =
                            let uu____7973 =
                              let uu____7979 =
                                let uu____7980 =
                                  let uu____7981 =
                                    let uu____7984 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    let uu____7985 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    (uu____7984, uu____7985) in
                                  FStar_SMTEncoding_Util.mkGT uu____7981 in
                                FStar_All.pipe_left
                                  FStar_SMTEncoding_Term.boxBool uu____7980 in
                              quant xy uu____7979 in
                            (FStar_Syntax_Const.op_GT, uu____7973) in
                          let uu____7991 =
                            let uu____8000 =
                              let uu____8008 =
                                let uu____8014 =
                                  let uu____8015 =
                                    let uu____8016 =
                                      let uu____8019 =
                                        FStar_SMTEncoding_Term.unboxInt x in
                                      let uu____8020 =
                                        FStar_SMTEncoding_Term.unboxInt y in
                                      (uu____8019, uu____8020) in
                                    FStar_SMTEncoding_Util.mkGTE uu____8016 in
                                  FStar_All.pipe_left
                                    FStar_SMTEncoding_Term.boxBool uu____8015 in
                                quant xy uu____8014 in
                              (FStar_Syntax_Const.op_GTE, uu____8008) in
                            let uu____8026 =
                              let uu____8035 =
                                let uu____8043 =
                                  let uu____8049 =
                                    let uu____8050 =
                                      let uu____8051 =
                                        let uu____8054 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        let uu____8055 =
                                          FStar_SMTEncoding_Term.unboxInt y in
                                        (uu____8054, uu____8055) in
                                      FStar_SMTEncoding_Util.mkSub uu____8051 in
                                    FStar_All.pipe_left
                                      FStar_SMTEncoding_Term.boxInt
                                      uu____8050 in
                                  quant xy uu____8049 in
                                (FStar_Syntax_Const.op_Subtraction,
                                  uu____8043) in
                              let uu____8061 =
                                let uu____8070 =
                                  let uu____8078 =
                                    let uu____8084 =
                                      let uu____8085 =
                                        let uu____8086 =
                                          FStar_SMTEncoding_Term.unboxInt x in
                                        FStar_SMTEncoding_Util.mkMinus
                                          uu____8086 in
                                      FStar_All.pipe_left
                                        FStar_SMTEncoding_Term.boxInt
                                        uu____8085 in
                                    quant qx uu____8084 in
                                  (FStar_Syntax_Const.op_Minus, uu____8078) in
                                let uu____8092 =
                                  let uu____8101 =
                                    let uu____8109 =
                                      let uu____8115 =
                                        let uu____8116 =
                                          let uu____8117 =
                                            let uu____8120 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                x in
                                            let uu____8121 =
                                              FStar_SMTEncoding_Term.unboxInt
                                                y in
                                            (uu____8120, uu____8121) in
                                          FStar_SMTEncoding_Util.mkAdd
                                            uu____8117 in
                                        FStar_All.pipe_left
                                          FStar_SMTEncoding_Term.boxInt
                                          uu____8116 in
                                      quant xy uu____8115 in
                                    (FStar_Syntax_Const.op_Addition,
                                      uu____8109) in
                                  let uu____8127 =
                                    let uu____8136 =
                                      let uu____8144 =
                                        let uu____8150 =
                                          let uu____8151 =
                                            let uu____8152 =
                                              let uu____8155 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  x in
                                              let uu____8156 =
                                                FStar_SMTEncoding_Term.unboxInt
                                                  y in
                                              (uu____8155, uu____8156) in
                                            FStar_SMTEncoding_Util.mkMul
                                              uu____8152 in
                                          FStar_All.pipe_left
                                            FStar_SMTEncoding_Term.boxInt
                                            uu____8151 in
                                        quant xy uu____8150 in
                                      (FStar_Syntax_Const.op_Multiply,
                                        uu____8144) in
                                    let uu____8162 =
                                      let uu____8171 =
                                        let uu____8179 =
                                          let uu____8185 =
                                            let uu____8186 =
                                              let uu____8187 =
                                                let uu____8190 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    x in
                                                let uu____8191 =
                                                  FStar_SMTEncoding_Term.unboxInt
                                                    y in
                                                (uu____8190, uu____8191) in
                                              FStar_SMTEncoding_Util.mkDiv
                                                uu____8187 in
                                            FStar_All.pipe_left
                                              FStar_SMTEncoding_Term.boxInt
                                              uu____8186 in
                                          quant xy uu____8185 in
                                        (FStar_Syntax_Const.op_Division,
                                          uu____8179) in
                                      let uu____8197 =
                                        let uu____8206 =
                                          let uu____8214 =
                                            let uu____8220 =
                                              let uu____8221 =
                                                let uu____8222 =
                                                  let uu____8225 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      x in
                                                  let uu____8226 =
                                                    FStar_SMTEncoding_Term.unboxInt
                                                      y in
                                                  (uu____8225, uu____8226) in
                                                FStar_SMTEncoding_Util.mkMod
                                                  uu____8222 in
                                              FStar_All.pipe_left
                                                FStar_SMTEncoding_Term.boxInt
                                                uu____8221 in
                                            quant xy uu____8220 in
                                          (FStar_Syntax_Const.op_Modulus,
                                            uu____8214) in
                                        let uu____8232 =
                                          let uu____8241 =
                                            let uu____8249 =
                                              let uu____8255 =
                                                let uu____8256 =
                                                  let uu____8257 =
                                                    let uu____8260 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        x in
                                                    let uu____8261 =
                                                      FStar_SMTEncoding_Term.unboxBool
                                                        y in
                                                    (uu____8260, uu____8261) in
                                                  FStar_SMTEncoding_Util.mkAnd
                                                    uu____8257 in
                                                FStar_All.pipe_left
                                                  FStar_SMTEncoding_Term.boxBool
                                                  uu____8256 in
                                              quant xy uu____8255 in
                                            (FStar_Syntax_Const.op_And,
                                              uu____8249) in
                                          let uu____8267 =
                                            let uu____8276 =
                                              let uu____8284 =
                                                let uu____8290 =
                                                  let uu____8291 =
                                                    let uu____8292 =
                                                      let uu____8295 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      let uu____8296 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          y in
                                                      (uu____8295,
                                                        uu____8296) in
                                                    FStar_SMTEncoding_Util.mkOr
                                                      uu____8292 in
                                                  FStar_All.pipe_left
                                                    FStar_SMTEncoding_Term.boxBool
                                                    uu____8291 in
                                                quant xy uu____8290 in
                                              (FStar_Syntax_Const.op_Or,
                                                uu____8284) in
                                            let uu____8302 =
                                              let uu____8311 =
                                                let uu____8319 =
                                                  let uu____8325 =
                                                    let uu____8326 =
                                                      let uu____8327 =
                                                        FStar_SMTEncoding_Term.unboxBool
                                                          x in
                                                      FStar_SMTEncoding_Util.mkNot
                                                        uu____8327 in
                                                    FStar_All.pipe_left
                                                      FStar_SMTEncoding_Term.boxBool
                                                      uu____8326 in
                                                  quant qx uu____8325 in
                                                (FStar_Syntax_Const.op_Negation,
                                                  uu____8319) in
                                              [uu____8311] in
                                            uu____8276 :: uu____8302 in
                                          uu____8241 :: uu____8267 in
                                        uu____8206 :: uu____8232 in
                                      uu____8171 :: uu____8197 in
                                    uu____8136 :: uu____8162 in
                                  uu____8101 :: uu____8127 in
                                uu____8070 :: uu____8092 in
                              uu____8035 :: uu____8061 in
                            uu____8000 :: uu____8026 in
                          uu____7965 :: uu____7991 in
                        uu____7930 :: uu____7956 in
                      uu____7895 :: uu____7921 in
                    uu____7864 :: uu____7886 in
                  uu____7834 :: uu____7855 in
                let mk1 l v1 =
                  let uu____8455 =
                    let uu____8460 =
                      FStar_All.pipe_right prims1
                        (FStar_List.find
                           (fun uu____8492  ->
                              match uu____8492 with
                              | (l',uu____8501) ->
                                  FStar_Ident.lid_equals l l')) in
                    FStar_All.pipe_right uu____8460
                      (FStar_Option.map
                         (fun uu____8534  ->
                            match uu____8534 with | (uu____8545,b) -> b v1)) in
                  FStar_All.pipe_right uu____8455 FStar_Option.get in
                let is l =
                  FStar_All.pipe_right prims1
                    (FStar_Util.for_some
                       (fun uu____8586  ->
                          match uu____8586 with
                          | (l',uu____8595) -> FStar_Ident.lid_equals l l')) in
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
        let uu____8621 = fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
        match uu____8621 with
        | (xxsym,xx) ->
            let uu____8626 = fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
            (match uu____8626 with
             | (ffsym,ff) ->
                 let xx_has_type =
                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff xx tapp in
                 let tapp_hash = FStar_SMTEncoding_Term.hash_of_term tapp in
                 let module_name = env.current_module_name in
                 let uu____8634 =
                   let uu____8638 =
                     let uu____8639 =
                       let uu____8645 =
                         let uu____8646 =
                           let uu____8649 =
                             let uu____8650 =
                               let uu____8653 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("PreType", [xx]) in
                               (tapp, uu____8653) in
                             FStar_SMTEncoding_Util.mkEq uu____8650 in
                           (xx_has_type, uu____8649) in
                         FStar_SMTEncoding_Util.mkImp uu____8646 in
                       ([[xx_has_type]],
                         ((xxsym, FStar_SMTEncoding_Term.Term_sort) ::
                         (ffsym, FStar_SMTEncoding_Term.Fuel_sort) :: vars),
                         uu____8645) in
                     FStar_SMTEncoding_Util.mkForall uu____8639 in
                   let uu____8666 =
                     let uu____8667 =
                       let uu____8668 =
                         let uu____8669 =
                           FStar_Util.digest_of_string tapp_hash in
                         Prims.strcat "_pretyping_" uu____8669 in
                       Prims.strcat module_name uu____8668 in
                     varops.mk_unique uu____8667 in
                   (uu____8638, (Some "pretyping"), uu____8666) in
                 FStar_SMTEncoding_Util.mkAssume uu____8634)
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
    let uu____8699 =
      let uu____8700 =
        let uu____8704 =
          FStar_SMTEncoding_Term.mk_HasType
            FStar_SMTEncoding_Term.mk_Term_unit tt in
        (uu____8704, (Some "unit typing"), "unit_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8700 in
    let uu____8706 =
      let uu____8708 =
        let uu____8709 =
          let uu____8713 =
            let uu____8714 =
              let uu____8720 =
                let uu____8721 =
                  let uu____8724 =
                    FStar_SMTEncoding_Util.mkEq
                      (x, FStar_SMTEncoding_Term.mk_Term_unit) in
                  (typing_pred, uu____8724) in
                FStar_SMTEncoding_Util.mkImp uu____8721 in
              ([[typing_pred]], [xx], uu____8720) in
            mkForall_fuel uu____8714 in
          (uu____8713, (Some "unit inversion"), "unit_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8709 in
      [uu____8708] in
    uu____8699 :: uu____8706 in
  let mk_bool env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.Bool_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8752 =
      let uu____8753 =
        let uu____8757 =
          let uu____8758 =
            let uu____8764 =
              let uu____8767 =
                let uu____8769 = FStar_SMTEncoding_Term.boxBool b in
                [uu____8769] in
              [uu____8767] in
            let uu____8772 =
              let uu____8773 = FStar_SMTEncoding_Term.boxBool b in
              FStar_SMTEncoding_Term.mk_HasType uu____8773 tt in
            (uu____8764, [bb], uu____8772) in
          FStar_SMTEncoding_Util.mkForall uu____8758 in
        (uu____8757, (Some "bool typing"), "bool_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8753 in
    let uu____8784 =
      let uu____8786 =
        let uu____8787 =
          let uu____8791 =
            let uu____8792 =
              let uu____8798 =
                let uu____8799 =
                  let uu____8802 =
                    FStar_SMTEncoding_Term.mk_tester "BoxBool" x in
                  (typing_pred, uu____8802) in
                FStar_SMTEncoding_Util.mkImp uu____8799 in
              ([[typing_pred]], [xx], uu____8798) in
            mkForall_fuel uu____8792 in
          (uu____8791, (Some "bool inversion"), "bool_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8787 in
      [uu____8786] in
    uu____8752 :: uu____8784 in
  let mk_int env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let typing_pred_y = FStar_SMTEncoding_Term.mk_HasType y tt in
    let aa = ("a", FStar_SMTEncoding_Term.Int_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let bb = ("b", FStar_SMTEncoding_Term.Int_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let precedes =
      let uu____8836 =
        let uu____8837 =
          let uu____8841 =
            let uu____8843 =
              let uu____8845 =
                let uu____8847 = FStar_SMTEncoding_Term.boxInt a in
                let uu____8848 =
                  let uu____8850 = FStar_SMTEncoding_Term.boxInt b in
                  [uu____8850] in
                uu____8847 :: uu____8848 in
              tt :: uu____8845 in
            tt :: uu____8843 in
          ("Prims.Precedes", uu____8841) in
        FStar_SMTEncoding_Util.mkApp uu____8837 in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8836 in
    let precedes_y_x =
      let uu____8853 = FStar_SMTEncoding_Util.mkApp ("Precedes", [y; x]) in
      FStar_All.pipe_left FStar_SMTEncoding_Term.mk_Valid uu____8853 in
    let uu____8855 =
      let uu____8856 =
        let uu____8860 =
          let uu____8861 =
            let uu____8867 =
              let uu____8870 =
                let uu____8872 = FStar_SMTEncoding_Term.boxInt b in
                [uu____8872] in
              [uu____8870] in
            let uu____8875 =
              let uu____8876 = FStar_SMTEncoding_Term.boxInt b in
              FStar_SMTEncoding_Term.mk_HasType uu____8876 tt in
            (uu____8867, [bb], uu____8875) in
          FStar_SMTEncoding_Util.mkForall uu____8861 in
        (uu____8860, (Some "int typing"), "int_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8856 in
    let uu____8887 =
      let uu____8889 =
        let uu____8890 =
          let uu____8894 =
            let uu____8895 =
              let uu____8901 =
                let uu____8902 =
                  let uu____8905 =
                    FStar_SMTEncoding_Term.mk_tester "BoxInt" x in
                  (typing_pred, uu____8905) in
                FStar_SMTEncoding_Util.mkImp uu____8902 in
              ([[typing_pred]], [xx], uu____8901) in
            mkForall_fuel uu____8895 in
          (uu____8894, (Some "int inversion"), "int_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____8890 in
      let uu____8918 =
        let uu____8920 =
          let uu____8921 =
            let uu____8925 =
              let uu____8926 =
                let uu____8932 =
                  let uu____8933 =
                    let uu____8936 =
                      let uu____8937 =
                        let uu____8939 =
                          let uu____8941 =
                            let uu____8943 =
                              let uu____8944 =
                                let uu____8947 =
                                  FStar_SMTEncoding_Term.unboxInt x in
                                let uu____8948 =
                                  FStar_SMTEncoding_Util.mkInteger'
                                    (Prims.parse_int "0") in
                                (uu____8947, uu____8948) in
                              FStar_SMTEncoding_Util.mkGT uu____8944 in
                            let uu____8949 =
                              let uu____8951 =
                                let uu____8952 =
                                  let uu____8955 =
                                    FStar_SMTEncoding_Term.unboxInt y in
                                  let uu____8956 =
                                    FStar_SMTEncoding_Util.mkInteger'
                                      (Prims.parse_int "0") in
                                  (uu____8955, uu____8956) in
                                FStar_SMTEncoding_Util.mkGTE uu____8952 in
                              let uu____8957 =
                                let uu____8959 =
                                  let uu____8960 =
                                    let uu____8963 =
                                      FStar_SMTEncoding_Term.unboxInt y in
                                    let uu____8964 =
                                      FStar_SMTEncoding_Term.unboxInt x in
                                    (uu____8963, uu____8964) in
                                  FStar_SMTEncoding_Util.mkLT uu____8960 in
                                [uu____8959] in
                              uu____8951 :: uu____8957 in
                            uu____8943 :: uu____8949 in
                          typing_pred_y :: uu____8941 in
                        typing_pred :: uu____8939 in
                      FStar_SMTEncoding_Util.mk_and_l uu____8937 in
                    (uu____8936, precedes_y_x) in
                  FStar_SMTEncoding_Util.mkImp uu____8933 in
                ([[typing_pred; typing_pred_y; precedes_y_x]], [xx; yy],
                  uu____8932) in
              mkForall_fuel uu____8926 in
            (uu____8925, (Some "well-founded ordering on nat (alt)"),
              "well-founded-ordering-on-nat") in
          FStar_SMTEncoding_Util.mkAssume uu____8921 in
        [uu____8920] in
      uu____8889 :: uu____8918 in
    uu____8855 :: uu____8887 in
  let mk_str env nm tt =
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x tt in
    let bb = ("b", FStar_SMTEncoding_Term.String_sort) in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let uu____8994 =
      let uu____8995 =
        let uu____8999 =
          let uu____9000 =
            let uu____9006 =
              let uu____9009 =
                let uu____9011 = FStar_SMTEncoding_Term.boxString b in
                [uu____9011] in
              [uu____9009] in
            let uu____9014 =
              let uu____9015 = FStar_SMTEncoding_Term.boxString b in
              FStar_SMTEncoding_Term.mk_HasType uu____9015 tt in
            (uu____9006, [bb], uu____9014) in
          FStar_SMTEncoding_Util.mkForall uu____9000 in
        (uu____8999, (Some "string typing"), "string_typing") in
      FStar_SMTEncoding_Util.mkAssume uu____8995 in
    let uu____9026 =
      let uu____9028 =
        let uu____9029 =
          let uu____9033 =
            let uu____9034 =
              let uu____9040 =
                let uu____9041 =
                  let uu____9044 =
                    FStar_SMTEncoding_Term.mk_tester "BoxString" x in
                  (typing_pred, uu____9044) in
                FStar_SMTEncoding_Util.mkImp uu____9041 in
              ([[typing_pred]], [xx], uu____9040) in
            mkForall_fuel uu____9034 in
          (uu____9033, (Some "string inversion"), "string_inversion") in
        FStar_SMTEncoding_Util.mkAssume uu____9029 in
      [uu____9028] in
    uu____8994 :: uu____9026 in
  let mk_ref1 env reft_name uu____9066 =
    let r = ("r", FStar_SMTEncoding_Term.Ref_sort) in
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let refa =
      let uu____9077 =
        let uu____9081 =
          let uu____9083 = FStar_SMTEncoding_Util.mkFreeV aa in [uu____9083] in
        (reft_name, uu____9081) in
      FStar_SMTEncoding_Util.mkApp uu____9077 in
    let refb =
      let uu____9086 =
        let uu____9090 =
          let uu____9092 = FStar_SMTEncoding_Util.mkFreeV bb in [uu____9092] in
        (reft_name, uu____9090) in
      FStar_SMTEncoding_Util.mkApp uu____9086 in
    let typing_pred = FStar_SMTEncoding_Term.mk_HasType x refa in
    let typing_pred_b = FStar_SMTEncoding_Term.mk_HasType x refb in
    let uu____9096 =
      let uu____9097 =
        let uu____9101 =
          let uu____9102 =
            let uu____9108 =
              let uu____9109 =
                let uu____9112 = FStar_SMTEncoding_Term.mk_tester "BoxRef" x in
                (typing_pred, uu____9112) in
              FStar_SMTEncoding_Util.mkImp uu____9109 in
            ([[typing_pred]], [xx; aa], uu____9108) in
          mkForall_fuel uu____9102 in
        (uu____9101, (Some "ref inversion"), "ref_inversion") in
      FStar_SMTEncoding_Util.mkAssume uu____9097 in
    [uu____9096] in
  let mk_true_interp env nm true_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [true_tm]) in
    [FStar_SMTEncoding_Util.mkAssume
       (valid, (Some "True interpretation"), "true_interp")] in
  let mk_false_interp env nm false_tm =
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [false_tm]) in
    let uu____9152 =
      let uu____9153 =
        let uu____9157 =
          FStar_SMTEncoding_Util.mkIff
            (FStar_SMTEncoding_Util.mkFalse, valid) in
        (uu____9157, (Some "False interpretation"), "false_interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9153 in
    [uu____9152] in
  let mk_and_interp env conj uu____9168 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_and_a_b = FStar_SMTEncoding_Util.mkApp (conj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_and_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9185 =
      let uu____9186 =
        let uu____9190 =
          let uu____9191 =
            let uu____9197 =
              let uu____9198 =
                let uu____9201 =
                  FStar_SMTEncoding_Util.mkAnd (valid_a, valid_b) in
                (uu____9201, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9198 in
            ([[l_and_a_b]], [aa; bb], uu____9197) in
          FStar_SMTEncoding_Util.mkForall uu____9191 in
        (uu____9190, (Some "/\\ interpretation"), "l_and-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9186 in
    [uu____9185] in
  let mk_or_interp env disj uu____9225 =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_or_a_b = FStar_SMTEncoding_Util.mkApp (disj, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_or_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9242 =
      let uu____9243 =
        let uu____9247 =
          let uu____9248 =
            let uu____9254 =
              let uu____9255 =
                let uu____9258 =
                  FStar_SMTEncoding_Util.mkOr (valid_a, valid_b) in
                (uu____9258, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9255 in
            ([[l_or_a_b]], [aa; bb], uu____9254) in
          FStar_SMTEncoding_Util.mkForall uu____9248 in
        (uu____9247, (Some "\\/ interpretation"), "l_or-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9243 in
    [uu____9242] in
  let mk_eq2_interp env eq2 tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let xx1 = ("x", FStar_SMTEncoding_Term.Term_sort) in
    let yy1 = ("y", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let x1 = FStar_SMTEncoding_Util.mkFreeV xx1 in
    let y1 = FStar_SMTEncoding_Util.mkFreeV yy1 in
    let eq2_x_y = FStar_SMTEncoding_Util.mkApp (eq2, [a; x1; y1]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [eq2_x_y]) in
    let uu____9299 =
      let uu____9300 =
        let uu____9304 =
          let uu____9305 =
            let uu____9311 =
              let uu____9312 =
                let uu____9315 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9315, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9312 in
            ([[eq2_x_y]], [aa; xx1; yy1], uu____9311) in
          FStar_SMTEncoding_Util.mkForall uu____9305 in
        (uu____9304, (Some "Eq2 interpretation"), "eq2-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9300 in
    [uu____9299] in
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
    let uu____9362 =
      let uu____9363 =
        let uu____9367 =
          let uu____9368 =
            let uu____9374 =
              let uu____9375 =
                let uu____9378 = FStar_SMTEncoding_Util.mkEq (x1, y1) in
                (uu____9378, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9375 in
            ([[eq3_x_y]], [aa; bb; xx1; yy1], uu____9374) in
          FStar_SMTEncoding_Util.mkForall uu____9368 in
        (uu____9367, (Some "Eq3 interpretation"), "eq3-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9363 in
    [uu____9362] in
  let mk_imp_interp env imp tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_imp_a_b = FStar_SMTEncoding_Util.mkApp (imp, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_imp_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9423 =
      let uu____9424 =
        let uu____9428 =
          let uu____9429 =
            let uu____9435 =
              let uu____9436 =
                let uu____9439 =
                  FStar_SMTEncoding_Util.mkImp (valid_a, valid_b) in
                (uu____9439, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9436 in
            ([[l_imp_a_b]], [aa; bb], uu____9435) in
          FStar_SMTEncoding_Util.mkForall uu____9429 in
        (uu____9428, (Some "==> interpretation"), "l_imp-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9424 in
    [uu____9423] in
  let mk_iff_interp env iff tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let bb = ("b", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let b = FStar_SMTEncoding_Util.mkFreeV bb in
    let l_iff_a_b = FStar_SMTEncoding_Util.mkApp (iff, [a; b]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_iff_a_b]) in
    let valid_a = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
    let valid_b = FStar_SMTEncoding_Util.mkApp ("Valid", [b]) in
    let uu____9480 =
      let uu____9481 =
        let uu____9485 =
          let uu____9486 =
            let uu____9492 =
              let uu____9493 =
                let uu____9496 =
                  FStar_SMTEncoding_Util.mkIff (valid_a, valid_b) in
                (uu____9496, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9493 in
            ([[l_iff_a_b]], [aa; bb], uu____9492) in
          FStar_SMTEncoding_Util.mkForall uu____9486 in
        (uu____9485, (Some "<==> interpretation"), "l_iff-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9481 in
    [uu____9480] in
  let mk_not_interp env l_not tt =
    let aa = ("a", FStar_SMTEncoding_Term.Term_sort) in
    let a = FStar_SMTEncoding_Util.mkFreeV aa in
    let l_not_a = FStar_SMTEncoding_Util.mkApp (l_not, [a]) in
    let valid = FStar_SMTEncoding_Util.mkApp ("Valid", [l_not_a]) in
    let not_valid_a =
      let uu____9530 = FStar_SMTEncoding_Util.mkApp ("Valid", [a]) in
      FStar_All.pipe_left FStar_SMTEncoding_Util.mkNot uu____9530 in
    let uu____9532 =
      let uu____9533 =
        let uu____9537 =
          let uu____9538 =
            let uu____9544 =
              FStar_SMTEncoding_Util.mkIff (not_valid_a, valid) in
            ([[l_not_a]], [aa], uu____9544) in
          FStar_SMTEncoding_Util.mkForall uu____9538 in
        (uu____9537, (Some "not interpretation"), "l_not-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9533 in
    [uu____9532] in
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
      let uu____9584 =
        let uu____9588 =
          let uu____9590 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9590] in
        ("Valid", uu____9588) in
      FStar_SMTEncoding_Util.mkApp uu____9584 in
    let uu____9592 =
      let uu____9593 =
        let uu____9597 =
          let uu____9598 =
            let uu____9604 =
              let uu____9605 =
                let uu____9608 =
                  let uu____9609 =
                    let uu____9615 =
                      let uu____9618 =
                        let uu____9620 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9620] in
                      [uu____9618] in
                    let uu____9623 =
                      let uu____9624 =
                        let uu____9627 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9627, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9624 in
                    (uu____9615, [xx1], uu____9623) in
                  FStar_SMTEncoding_Util.mkForall uu____9609 in
                (uu____9608, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9605 in
            ([[l_forall_a_b]], [aa; bb], uu____9604) in
          FStar_SMTEncoding_Util.mkForall uu____9598 in
        (uu____9597, (Some "forall interpretation"), "forall-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9593 in
    [uu____9592] in
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
      let uu____9678 =
        let uu____9682 =
          let uu____9684 = FStar_SMTEncoding_Util.mk_ApplyTT b x1 in
          [uu____9684] in
        ("Valid", uu____9682) in
      FStar_SMTEncoding_Util.mkApp uu____9678 in
    let uu____9686 =
      let uu____9687 =
        let uu____9691 =
          let uu____9692 =
            let uu____9698 =
              let uu____9699 =
                let uu____9702 =
                  let uu____9703 =
                    let uu____9709 =
                      let uu____9712 =
                        let uu____9714 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        [uu____9714] in
                      [uu____9712] in
                    let uu____9717 =
                      let uu____9718 =
                        let uu____9721 =
                          FStar_SMTEncoding_Term.mk_HasTypeZ x1 a in
                        (uu____9721, valid_b_x) in
                      FStar_SMTEncoding_Util.mkImp uu____9718 in
                    (uu____9709, [xx1], uu____9717) in
                  FStar_SMTEncoding_Util.mkExists uu____9703 in
                (uu____9702, valid) in
              FStar_SMTEncoding_Util.mkIff uu____9699 in
            ([[l_exists_a_b]], [aa; bb], uu____9698) in
          FStar_SMTEncoding_Util.mkForall uu____9692 in
        (uu____9691, (Some "exists interpretation"), "exists-interp") in
      FStar_SMTEncoding_Util.mkAssume uu____9687 in
    [uu____9686] in
  let mk_range_interp env range tt =
    let range_ty = FStar_SMTEncoding_Util.mkApp (range, []) in
    let uu____9757 =
      let uu____9758 =
        let uu____9762 =
          FStar_SMTEncoding_Term.mk_HasTypeZ
            FStar_SMTEncoding_Term.mk_Range_const range_ty in
        let uu____9763 = varops.mk_unique "typing_range_const" in
        (uu____9762, (Some "Range_const typing"), uu____9763) in
      FStar_SMTEncoding_Util.mkAssume uu____9758 in
    [uu____9757] in
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
          let uu____10025 =
            FStar_Util.find_opt
              (fun uu____10043  ->
                 match uu____10043 with
                 | (l,uu____10053) -> FStar_Ident.lid_equals l t) prims1 in
          match uu____10025 with
          | None  -> []
          | Some (uu____10075,f) -> f env s tt
let encode_smt_lemma:
  env_t ->
    FStar_Syntax_Syntax.fv ->
      FStar_Syntax_Syntax.typ -> FStar_SMTEncoding_Term.decl Prims.list
  =
  fun env  ->
    fun fv  ->
      fun t  ->
        let lid = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
        let uu____10112 = encode_function_type_as_formula t env in
        match uu____10112 with
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
            let uu____10144 =
              (let uu____10145 =
                 (FStar_Syntax_Util.is_pure_or_ghost_function t_norm) ||
                   (FStar_TypeChecker_Env.is_reifiable_function env.tcenv
                      t_norm) in
               FStar_All.pipe_left Prims.op_Negation uu____10145) ||
                (FStar_Syntax_Util.is_lemma t_norm) in
            if uu____10144
            then
              let uu____10149 = new_term_constant_and_tok_from_lid env lid in
              match uu____10149 with
              | (vname,vtok,env1) ->
                  let arg_sorts =
                    let uu____10161 =
                      let uu____10162 = FStar_Syntax_Subst.compress t_norm in
                      uu____10162.FStar_Syntax_Syntax.n in
                    match uu____10161 with
                    | FStar_Syntax_Syntax.Tm_arrow (binders,uu____10167) ->
                        FStar_All.pipe_right binders
                          (FStar_List.map
                             (fun uu____10184  ->
                                FStar_SMTEncoding_Term.Term_sort))
                    | uu____10187 -> [] in
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
              (let uu____10196 = prims.is lid in
               if uu____10196
               then
                 let vname = varops.new_fvar lid in
                 let uu____10201 = prims.mk lid vname in
                 match uu____10201 with
                 | (tok,definition) ->
                     let env1 = push_free_var env lid vname (Some tok) in
                     (definition, env1)
               else
                 (let encode_non_total_function_typ =
                    lid.FStar_Ident.nsstr <> "Prims" in
                  let uu____10216 =
                    let uu____10222 = curried_arrow_formals_comp t_norm in
                    match uu____10222 with
                    | (args,comp) ->
                        let comp1 =
                          let uu____10233 =
                            FStar_TypeChecker_Env.is_reifiable_comp env.tcenv
                              comp in
                          if uu____10233
                          then
                            let uu____10234 =
                              FStar_TypeChecker_Env.reify_comp
                                (let uu___144_10235 = env.tcenv in
                                 {
                                   FStar_TypeChecker_Env.solver =
                                     (uu___144_10235.FStar_TypeChecker_Env.solver);
                                   FStar_TypeChecker_Env.range =
                                     (uu___144_10235.FStar_TypeChecker_Env.range);
                                   FStar_TypeChecker_Env.curmodule =
                                     (uu___144_10235.FStar_TypeChecker_Env.curmodule);
                                   FStar_TypeChecker_Env.gamma =
                                     (uu___144_10235.FStar_TypeChecker_Env.gamma);
                                   FStar_TypeChecker_Env.gamma_cache =
                                     (uu___144_10235.FStar_TypeChecker_Env.gamma_cache);
                                   FStar_TypeChecker_Env.modules =
                                     (uu___144_10235.FStar_TypeChecker_Env.modules);
                                   FStar_TypeChecker_Env.expected_typ =
                                     (uu___144_10235.FStar_TypeChecker_Env.expected_typ);
                                   FStar_TypeChecker_Env.sigtab =
                                     (uu___144_10235.FStar_TypeChecker_Env.sigtab);
                                   FStar_TypeChecker_Env.is_pattern =
                                     (uu___144_10235.FStar_TypeChecker_Env.is_pattern);
                                   FStar_TypeChecker_Env.instantiate_imp =
                                     (uu___144_10235.FStar_TypeChecker_Env.instantiate_imp);
                                   FStar_TypeChecker_Env.effects =
                                     (uu___144_10235.FStar_TypeChecker_Env.effects);
                                   FStar_TypeChecker_Env.generalize =
                                     (uu___144_10235.FStar_TypeChecker_Env.generalize);
                                   FStar_TypeChecker_Env.letrecs =
                                     (uu___144_10235.FStar_TypeChecker_Env.letrecs);
                                   FStar_TypeChecker_Env.top_level =
                                     (uu___144_10235.FStar_TypeChecker_Env.top_level);
                                   FStar_TypeChecker_Env.check_uvars =
                                     (uu___144_10235.FStar_TypeChecker_Env.check_uvars);
                                   FStar_TypeChecker_Env.use_eq =
                                     (uu___144_10235.FStar_TypeChecker_Env.use_eq);
                                   FStar_TypeChecker_Env.is_iface =
                                     (uu___144_10235.FStar_TypeChecker_Env.is_iface);
                                   FStar_TypeChecker_Env.admit =
                                     (uu___144_10235.FStar_TypeChecker_Env.admit);
                                   FStar_TypeChecker_Env.lax = true;
                                   FStar_TypeChecker_Env.lax_universes =
                                     (uu___144_10235.FStar_TypeChecker_Env.lax_universes);
                                   FStar_TypeChecker_Env.type_of =
                                     (uu___144_10235.FStar_TypeChecker_Env.type_of);
                                   FStar_TypeChecker_Env.universe_of =
                                     (uu___144_10235.FStar_TypeChecker_Env.universe_of);
                                   FStar_TypeChecker_Env.use_bv_sorts =
                                     (uu___144_10235.FStar_TypeChecker_Env.use_bv_sorts);
                                   FStar_TypeChecker_Env.qname_and_index =
                                     (uu___144_10235.FStar_TypeChecker_Env.qname_and_index)
                                 }) comp FStar_Syntax_Syntax.U_unknown in
                            FStar_Syntax_Syntax.mk_Total uu____10234
                          else comp in
                        if encode_non_total_function_typ
                        then
                          let uu____10242 =
                            FStar_TypeChecker_Util.pure_or_ghost_pre_and_post
                              env.tcenv comp1 in
                          (args, uu____10242)
                        else
                          (args,
                            (None, (FStar_Syntax_Util.comp_result comp1))) in
                  match uu____10216 with
                  | (formals,(pre_opt,res_t)) ->
                      let uu____10269 =
                        new_term_constant_and_tok_from_lid env lid in
                      (match uu____10269 with
                       | (vname,vtok,env1) ->
                           let vtok_tm =
                             match formals with
                             | [] ->
                                 FStar_SMTEncoding_Util.mkFreeV
                                   (vname, FStar_SMTEncoding_Term.Term_sort)
                             | uu____10282 ->
                                 FStar_SMTEncoding_Util.mkApp (vtok, []) in
                           let mk_disc_proj_axioms guard encoded_res_t vapp
                             vars =
                             FStar_All.pipe_right quals
                               (FStar_List.collect
                                  (fun uu___115_10306  ->
                                     match uu___115_10306 with
                                     | FStar_Syntax_Syntax.Discriminator d ->
                                         let uu____10309 =
                                           FStar_Util.prefix vars in
                                         (match uu____10309 with
                                          | (uu____10320,(xxsym,uu____10322))
                                              ->
                                              let xx =
                                                FStar_SMTEncoding_Util.mkFreeV
                                                  (xxsym,
                                                    FStar_SMTEncoding_Term.Term_sort) in
                                              let uu____10332 =
                                                let uu____10333 =
                                                  let uu____10337 =
                                                    let uu____10338 =
                                                      let uu____10344 =
                                                        let uu____10345 =
                                                          let uu____10348 =
                                                            let uu____10349 =
                                                              FStar_SMTEncoding_Term.mk_tester
                                                                (escape
                                                                   d.FStar_Ident.str)
                                                                xx in
                                                            FStar_All.pipe_left
                                                              FStar_SMTEncoding_Term.boxBool
                                                              uu____10349 in
                                                          (vapp, uu____10348) in
                                                        FStar_SMTEncoding_Util.mkEq
                                                          uu____10345 in
                                                      ([[vapp]], vars,
                                                        uu____10344) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10338 in
                                                  (uu____10337,
                                                    (Some
                                                       "Discriminator equation"),
                                                    (Prims.strcat
                                                       "disc_equation_"
                                                       (escape
                                                          d.FStar_Ident.str))) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10333 in
                                              [uu____10332])
                                     | FStar_Syntax_Syntax.Projector 
                                         (d,f) ->
                                         let uu____10360 =
                                           FStar_Util.prefix vars in
                                         (match uu____10360 with
                                          | (uu____10371,(xxsym,uu____10373))
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
                                              let uu____10387 =
                                                let uu____10388 =
                                                  let uu____10392 =
                                                    let uu____10393 =
                                                      let uu____10399 =
                                                        FStar_SMTEncoding_Util.mkEq
                                                          (vapp, prim_app) in
                                                      ([[vapp]], vars,
                                                        uu____10399) in
                                                    FStar_SMTEncoding_Util.mkForall
                                                      uu____10393 in
                                                  (uu____10392,
                                                    (Some
                                                       "Projector equation"),
                                                    (Prims.strcat
                                                       "proj_equation_"
                                                       tp_name)) in
                                                FStar_SMTEncoding_Util.mkAssume
                                                  uu____10388 in
                                              [uu____10387])
                                     | uu____10408 -> [])) in
                           let uu____10409 = encode_binders None formals env1 in
                           (match uu____10409 with
                            | (vars,guards,env',decls1,uu____10425) ->
                                let uu____10432 =
                                  match pre_opt with
                                  | None  ->
                                      let uu____10437 =
                                        FStar_SMTEncoding_Util.mk_and_l
                                          guards in
                                      (uu____10437, decls1)
                                  | Some p ->
                                      let uu____10439 = encode_formula p env' in
                                      (match uu____10439 with
                                       | (g,ds) ->
                                           let uu____10446 =
                                             FStar_SMTEncoding_Util.mk_and_l
                                               (g :: guards) in
                                           (uu____10446,
                                             (FStar_List.append decls1 ds))) in
                                (match uu____10432 with
                                 | (guard,decls11) ->
                                     let vtok_app = mk_Apply vtok_tm vars in
                                     let vapp =
                                       let uu____10455 =
                                         let uu____10459 =
                                           FStar_List.map
                                             FStar_SMTEncoding_Util.mkFreeV
                                             vars in
                                         (vname, uu____10459) in
                                       FStar_SMTEncoding_Util.mkApp
                                         uu____10455 in
                                     let uu____10464 =
                                       let vname_decl =
                                         let uu____10469 =
                                           let uu____10475 =
                                             FStar_All.pipe_right formals
                                               (FStar_List.map
                                                  (fun uu____10480  ->
                                                     FStar_SMTEncoding_Term.Term_sort)) in
                                           (vname, uu____10475,
                                             FStar_SMTEncoding_Term.Term_sort,
                                             None) in
                                         FStar_SMTEncoding_Term.DeclFun
                                           uu____10469 in
                                       let uu____10485 =
                                         let env2 =
                                           let uu___145_10489 = env1 in
                                           {
                                             bindings =
                                               (uu___145_10489.bindings);
                                             depth = (uu___145_10489.depth);
                                             tcenv = (uu___145_10489.tcenv);
                                             warn = (uu___145_10489.warn);
                                             cache = (uu___145_10489.cache);
                                             nolabels =
                                               (uu___145_10489.nolabels);
                                             use_zfuel_name =
                                               (uu___145_10489.use_zfuel_name);
                                             encode_non_total_function_typ;
                                             current_module_name =
                                               (uu___145_10489.current_module_name)
                                           } in
                                         let uu____10490 =
                                           let uu____10491 =
                                             head_normal env2 tt in
                                           Prims.op_Negation uu____10491 in
                                         if uu____10490
                                         then
                                           encode_term_pred None tt env2
                                             vtok_tm
                                         else
                                           encode_term_pred None t_norm env2
                                             vtok_tm in
                                       match uu____10485 with
                                       | (tok_typing,decls2) ->
                                           let tok_typing1 =
                                             match formals with
                                             | uu____10501::uu____10502 ->
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
                                                   let uu____10525 =
                                                     let uu____10531 =
                                                       FStar_SMTEncoding_Term.mk_NoHoist
                                                         f tok_typing in
                                                     ([[vtok_app_l];
                                                      [vtok_app_r]], 
                                                       [ff], uu____10531) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____10525 in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (guarded_tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname))
                                             | uu____10545 ->
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   (tok_typing,
                                                     (Some
                                                        "function token typing"),
                                                     (Prims.strcat
                                                        "function_token_typing_"
                                                        vname)) in
                                           let uu____10547 =
                                             match formals with
                                             | [] ->
                                                 let uu____10556 =
                                                   let uu____10557 =
                                                     let uu____10559 =
                                                       FStar_SMTEncoding_Util.mkFreeV
                                                         (vname,
                                                           FStar_SMTEncoding_Term.Term_sort) in
                                                     FStar_All.pipe_left
                                                       (fun _0_34  ->
                                                          Some _0_34)
                                                       uu____10559 in
                                                   push_free_var env1 lid
                                                     vname uu____10557 in
                                                 ((FStar_List.append decls2
                                                     [tok_typing1]),
                                                   uu____10556)
                                             | uu____10562 ->
                                                 let vtok_decl =
                                                   FStar_SMTEncoding_Term.DeclFun
                                                     (vtok, [],
                                                       FStar_SMTEncoding_Term.Term_sort,
                                                       None) in
                                                 let vtok_fresh =
                                                   let uu____10567 =
                                                     varops.next_id () in
                                                   FStar_SMTEncoding_Term.fresh_token
                                                     (vtok,
                                                       FStar_SMTEncoding_Term.Term_sort)
                                                     uu____10567 in
                                                 let name_tok_corr =
                                                   let uu____10569 =
                                                     let uu____10573 =
                                                       let uu____10574 =
                                                         let uu____10580 =
                                                           FStar_SMTEncoding_Util.mkEq
                                                             (vtok_app, vapp) in
                                                         ([[vtok_app];
                                                          [vapp]], vars,
                                                           uu____10580) in
                                                       FStar_SMTEncoding_Util.mkForall
                                                         uu____10574 in
                                                     (uu____10573,
                                                       (Some
                                                          "Name-token correspondence"),
                                                       (Prims.strcat
                                                          "token_correspondence_"
                                                          vname)) in
                                                   FStar_SMTEncoding_Util.mkAssume
                                                     uu____10569 in
                                                 ((FStar_List.append decls2
                                                     [vtok_decl;
                                                     vtok_fresh;
                                                     name_tok_corr;
                                                     tok_typing1]), env1) in
                                           (match uu____10547 with
                                            | (tok_decl,env2) ->
                                                ((vname_decl :: tok_decl),
                                                  env2)) in
                                     (match uu____10464 with
                                      | (decls2,env2) ->
                                          let uu____10604 =
                                            let res_t1 =
                                              FStar_Syntax_Subst.compress
                                                res_t in
                                            let uu____10609 =
                                              encode_term res_t1 env' in
                                            match uu____10609 with
                                            | (encoded_res_t,decls) ->
                                                let uu____10617 =
                                                  FStar_SMTEncoding_Term.mk_HasType
                                                    vapp encoded_res_t in
                                                (encoded_res_t, uu____10617,
                                                  decls) in
                                          (match uu____10604 with
                                           | (encoded_res_t,ty_pred,decls3)
                                               ->
                                               let typingAx =
                                                 let uu____10625 =
                                                   let uu____10629 =
                                                     let uu____10630 =
                                                       let uu____10636 =
                                                         FStar_SMTEncoding_Util.mkImp
                                                           (guard, ty_pred) in
                                                       ([[vapp]], vars,
                                                         uu____10636) in
                                                     FStar_SMTEncoding_Util.mkForall
                                                       uu____10630 in
                                                   (uu____10629,
                                                     (Some "free var typing"),
                                                     (Prims.strcat "typing_"
                                                        vname)) in
                                                 FStar_SMTEncoding_Util.mkAssume
                                                   uu____10625 in
                                               let freshness =
                                                 let uu____10645 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.New) in
                                                 if uu____10645
                                                 then
                                                   let uu____10648 =
                                                     let uu____10649 =
                                                       let uu____10655 =
                                                         FStar_All.pipe_right
                                                           vars
                                                           (FStar_List.map
                                                              FStar_Pervasives.snd) in
                                                       let uu____10661 =
                                                         varops.next_id () in
                                                       (vname, uu____10655,
                                                         FStar_SMTEncoding_Term.Term_sort,
                                                         uu____10661) in
                                                     FStar_SMTEncoding_Term.fresh_constructor
                                                       uu____10649 in
                                                   let uu____10663 =
                                                     let uu____10665 =
                                                       pretype_axiom env2
                                                         vapp vars in
                                                     [uu____10665] in
                                                   uu____10648 :: uu____10663
                                                 else [] in
                                               let g =
                                                 let uu____10669 =
                                                   let uu____10671 =
                                                     let uu____10673 =
                                                       let uu____10675 =
                                                         let uu____10677 =
                                                           mk_disc_proj_axioms
                                                             guard
                                                             encoded_res_t
                                                             vapp vars in
                                                         typingAx ::
                                                           uu____10677 in
                                                       FStar_List.append
                                                         freshness
                                                         uu____10675 in
                                                     FStar_List.append decls3
                                                       uu____10673 in
                                                   FStar_List.append decls2
                                                     uu____10671 in
                                                 FStar_List.append decls11
                                                   uu____10669 in
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
          let uu____10699 =
            try_lookup_lid env
              (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          match uu____10699 with
          | None  ->
              let uu____10722 = encode_free_var env x t t_norm [] in
              (match uu____10722 with
               | (decls,env1) ->
                   let uu____10737 =
                     lookup_lid env1
                       (x.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                   (match uu____10737 with
                    | (n1,x',uu____10756) -> ((n1, x'), decls, env1)))
          | Some (n1,x1,uu____10768) -> ((n1, x1), [], env)
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
          let uu____10801 = encode_free_var env lid t tt quals in
          match uu____10801 with
          | (decls,env1) ->
              let uu____10812 = FStar_Syntax_Util.is_smt_lemma t in
              if uu____10812
              then
                let uu____10816 =
                  let uu____10818 = encode_smt_lemma env1 lid tt in
                  FStar_List.append decls uu____10818 in
                (uu____10816, env1)
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
             (fun uu____10846  ->
                fun lb  ->
                  match uu____10846 with
                  | (decls,env1) ->
                      let uu____10858 =
                        let uu____10862 =
                          FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                        encode_top_level_val env1 uu____10862
                          lb.FStar_Syntax_Syntax.lbtyp quals in
                      (match uu____10858 with
                       | (decls',env2) ->
                           ((FStar_List.append decls decls'), env2)))
             ([], env))
let is_tactic: FStar_Syntax_Syntax.term -> Prims.bool =
  fun t  ->
    let fstar_tactics_tactic_lid =
      FStar_Syntax_Const.p2l ["FStar"; "Tactics"; "tactic"] in
    let uu____10876 = FStar_Syntax_Util.head_and_args t in
    match uu____10876 with
    | (hd1,args) ->
        let uu____10902 =
          let uu____10903 = FStar_Syntax_Util.un_uinst hd1 in
          uu____10903.FStar_Syntax_Syntax.n in
        (match uu____10902 with
         | FStar_Syntax_Syntax.Tm_fvar fv when
             FStar_Syntax_Syntax.fv_eq_lid fv fstar_tactics_tactic_lid ->
             true
         | FStar_Syntax_Syntax.Tm_arrow (uu____10907,c) ->
             let effect_name = FStar_Syntax_Util.comp_effect_name c in
             FStar_Util.starts_with "FStar.Tactics"
               effect_name.FStar_Ident.str
         | uu____10920 -> false)
let encode_top_level_let:
  env_t ->
    (Prims.bool* FStar_Syntax_Syntax.letbinding Prims.list) ->
      FStar_Syntax_Syntax.qualifier Prims.list ->
        (FStar_SMTEncoding_Term.decl Prims.list* env_t)
  =
  fun env  ->
    fun uu____10935  ->
      fun quals  ->
        match uu____10935 with
        | (is_rec,bindings) ->
            let eta_expand1 binders formals body t =
              let nbinders = FStar_List.length binders in
              let uu____10984 = FStar_Util.first_N nbinders formals in
              match uu____10984 with
              | (formals1,extra_formals) ->
                  let subst1 =
                    FStar_List.map2
                      (fun uu____11024  ->
                         fun uu____11025  ->
                           match (uu____11024, uu____11025) with
                           | ((formal,uu____11035),(binder,uu____11037)) ->
                               let uu____11042 =
                                 let uu____11047 =
                                   FStar_Syntax_Syntax.bv_to_name binder in
                                 (formal, uu____11047) in
                               FStar_Syntax_Syntax.NT uu____11042) formals1
                      binders in
                  let extra_formals1 =
                    let uu____11052 =
                      FStar_All.pipe_right extra_formals
                        (FStar_List.map
                           (fun uu____11066  ->
                              match uu____11066 with
                              | (x,i) ->
                                  let uu____11073 =
                                    let uu___146_11074 = x in
                                    let uu____11075 =
                                      FStar_Syntax_Subst.subst subst1
                                        x.FStar_Syntax_Syntax.sort in
                                    {
                                      FStar_Syntax_Syntax.ppname =
                                        (uu___146_11074.FStar_Syntax_Syntax.ppname);
                                      FStar_Syntax_Syntax.index =
                                        (uu___146_11074.FStar_Syntax_Syntax.index);
                                      FStar_Syntax_Syntax.sort = uu____11075
                                    } in
                                  (uu____11073, i))) in
                    FStar_All.pipe_right uu____11052
                      FStar_Syntax_Util.name_binders in
                  let body1 =
                    let uu____11087 =
                      let uu____11089 =
                        let uu____11090 = FStar_Syntax_Subst.subst subst1 t in
                        uu____11090.FStar_Syntax_Syntax.n in
                      FStar_All.pipe_left (fun _0_35  -> Some _0_35)
                        uu____11089 in
                    let uu____11094 =
                      let uu____11095 = FStar_Syntax_Subst.compress body in
                      let uu____11096 =
                        let uu____11097 =
                          FStar_Syntax_Util.args_of_binders extra_formals1 in
                        FStar_All.pipe_left FStar_Pervasives.snd uu____11097 in
                      FStar_Syntax_Syntax.extend_app_n uu____11095
                        uu____11096 in
                    uu____11094 uu____11087 body.FStar_Syntax_Syntax.pos in
                  ((FStar_List.append binders extra_formals1), body1) in
            let destruct_bound_function flid t_norm e =
              let get_result_type c =
                let uu____11139 =
                  FStar_TypeChecker_Env.is_reifiable_comp env.tcenv c in
                if uu____11139
                then
                  FStar_TypeChecker_Env.reify_comp
                    (let uu___147_11140 = env.tcenv in
                     {
                       FStar_TypeChecker_Env.solver =
                         (uu___147_11140.FStar_TypeChecker_Env.solver);
                       FStar_TypeChecker_Env.range =
                         (uu___147_11140.FStar_TypeChecker_Env.range);
                       FStar_TypeChecker_Env.curmodule =
                         (uu___147_11140.FStar_TypeChecker_Env.curmodule);
                       FStar_TypeChecker_Env.gamma =
                         (uu___147_11140.FStar_TypeChecker_Env.gamma);
                       FStar_TypeChecker_Env.gamma_cache =
                         (uu___147_11140.FStar_TypeChecker_Env.gamma_cache);
                       FStar_TypeChecker_Env.modules =
                         (uu___147_11140.FStar_TypeChecker_Env.modules);
                       FStar_TypeChecker_Env.expected_typ =
                         (uu___147_11140.FStar_TypeChecker_Env.expected_typ);
                       FStar_TypeChecker_Env.sigtab =
                         (uu___147_11140.FStar_TypeChecker_Env.sigtab);
                       FStar_TypeChecker_Env.is_pattern =
                         (uu___147_11140.FStar_TypeChecker_Env.is_pattern);
                       FStar_TypeChecker_Env.instantiate_imp =
                         (uu___147_11140.FStar_TypeChecker_Env.instantiate_imp);
                       FStar_TypeChecker_Env.effects =
                         (uu___147_11140.FStar_TypeChecker_Env.effects);
                       FStar_TypeChecker_Env.generalize =
                         (uu___147_11140.FStar_TypeChecker_Env.generalize);
                       FStar_TypeChecker_Env.letrecs =
                         (uu___147_11140.FStar_TypeChecker_Env.letrecs);
                       FStar_TypeChecker_Env.top_level =
                         (uu___147_11140.FStar_TypeChecker_Env.top_level);
                       FStar_TypeChecker_Env.check_uvars =
                         (uu___147_11140.FStar_TypeChecker_Env.check_uvars);
                       FStar_TypeChecker_Env.use_eq =
                         (uu___147_11140.FStar_TypeChecker_Env.use_eq);
                       FStar_TypeChecker_Env.is_iface =
                         (uu___147_11140.FStar_TypeChecker_Env.is_iface);
                       FStar_TypeChecker_Env.admit =
                         (uu___147_11140.FStar_TypeChecker_Env.admit);
                       FStar_TypeChecker_Env.lax = true;
                       FStar_TypeChecker_Env.lax_universes =
                         (uu___147_11140.FStar_TypeChecker_Env.lax_universes);
                       FStar_TypeChecker_Env.type_of =
                         (uu___147_11140.FStar_TypeChecker_Env.type_of);
                       FStar_TypeChecker_Env.universe_of =
                         (uu___147_11140.FStar_TypeChecker_Env.universe_of);
                       FStar_TypeChecker_Env.use_bv_sorts =
                         (uu___147_11140.FStar_TypeChecker_Env.use_bv_sorts);
                       FStar_TypeChecker_Env.qname_and_index =
                         (uu___147_11140.FStar_TypeChecker_Env.qname_and_index)
                     }) c FStar_Syntax_Syntax.U_unknown
                else FStar_Syntax_Util.comp_result c in
              let rec aux norm1 t_norm1 =
                let uu____11161 = FStar_Syntax_Util.abs_formals e in
                match uu____11161 with
                | (binders,body,lopt) ->
                    (match binders with
                     | uu____11210::uu____11211 ->
                         let uu____11219 =
                           let uu____11220 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11220.FStar_Syntax_Syntax.n in
                         (match uu____11219 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11247 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11247 with
                               | (formals1,c1) ->
                                   let nformals = FStar_List.length formals1 in
                                   let nbinders = FStar_List.length binders in
                                   let tres = get_result_type c1 in
                                   let uu____11273 =
                                     (nformals < nbinders) &&
                                       (FStar_Syntax_Util.is_total_comp c1) in
                                   if uu____11273
                                   then
                                     let uu____11291 =
                                       FStar_Util.first_N nformals binders in
                                     (match uu____11291 with
                                      | (bs0,rest) ->
                                          let c2 =
                                            let subst1 =
                                              FStar_List.map2
                                                (fun uu____11337  ->
                                                   fun uu____11338  ->
                                                     match (uu____11337,
                                                             uu____11338)
                                                     with
                                                     | ((x,uu____11348),
                                                        (b,uu____11350)) ->
                                                         let uu____11355 =
                                                           let uu____11360 =
                                                             FStar_Syntax_Syntax.bv_to_name
                                                               b in
                                                           (x, uu____11360) in
                                                         FStar_Syntax_Syntax.NT
                                                           uu____11355)
                                                formals1 bs0 in
                                            FStar_Syntax_Subst.subst_comp
                                              subst1 c1 in
                                          let body1 =
                                            FStar_Syntax_Util.abs rest body
                                              lopt in
                                          let uu____11362 =
                                            let uu____11373 =
                                              get_result_type c2 in
                                            (bs0, body1, bs0, uu____11373) in
                                          (uu____11362, false))
                                   else
                                     if nformals > nbinders
                                     then
                                       (let uu____11408 =
                                          eta_expand1 binders formals1 body
                                            tres in
                                        match uu____11408 with
                                        | (binders1,body1) ->
                                            ((binders1, body1, formals1,
                                               tres), false))
                                     else
                                       ((binders, body, formals1, tres),
                                         false))
                          | FStar_Syntax_Syntax.Tm_refine (x,uu____11460) ->
                              let uu____11465 =
                                let uu____11476 =
                                  aux norm1 x.FStar_Syntax_Syntax.sort in
                                fst uu____11476 in
                              (uu____11465, true)
                          | uu____11509 when Prims.op_Negation norm1 ->
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
                          | uu____11511 ->
                              let uu____11512 =
                                let uu____11513 =
                                  FStar_Syntax_Print.term_to_string e in
                                let uu____11514 =
                                  FStar_Syntax_Print.term_to_string t_norm1 in
                                FStar_Util.format3
                                  "Impossible! let-bound lambda %s = %s has a type that's not a function: %s\n"
                                  flid.FStar_Ident.str uu____11513
                                  uu____11514 in
                              failwith uu____11512)
                     | uu____11527 ->
                         let uu____11528 =
                           let uu____11529 =
                             FStar_Syntax_Subst.compress t_norm1 in
                           uu____11529.FStar_Syntax_Syntax.n in
                         (match uu____11528 with
                          | FStar_Syntax_Syntax.Tm_arrow (formals,c) ->
                              let uu____11556 =
                                FStar_Syntax_Subst.open_comp formals c in
                              (match uu____11556 with
                               | (formals1,c1) ->
                                   let tres = get_result_type c1 in
                                   let uu____11574 =
                                     eta_expand1 [] formals1 e tres in
                                   (match uu____11574 with
                                    | (binders1,body1) ->
                                        ((binders1, body1, formals1, tres),
                                          false)))
                          | uu____11622 -> (([], e, [], t_norm1), false))) in
              aux false t_norm in
            (try
               let uu____11650 =
                 FStar_All.pipe_right bindings
                   (FStar_Util.for_all
                      (fun lb  ->
                         (FStar_Syntax_Util.is_lemma
                            lb.FStar_Syntax_Syntax.lbtyp)
                           || (is_tactic lb.FStar_Syntax_Syntax.lbtyp))) in
               if uu____11650
               then encode_top_level_vals env bindings quals
               else
                 (let uu____11657 =
                    FStar_All.pipe_right bindings
                      (FStar_List.fold_left
                         (fun uu____11698  ->
                            fun lb  ->
                              match uu____11698 with
                              | (toks,typs,decls,env1) ->
                                  ((let uu____11749 =
                                      FStar_Syntax_Util.is_lemma
                                        lb.FStar_Syntax_Syntax.lbtyp in
                                    if uu____11749
                                    then raise Let_rec_unencodeable
                                    else ());
                                   (let t_norm =
                                      whnf env1 lb.FStar_Syntax_Syntax.lbtyp in
                                    let uu____11752 =
                                      let uu____11760 =
                                        FStar_Util.right
                                          lb.FStar_Syntax_Syntax.lbname in
                                      declare_top_level_let env1 uu____11760
                                        lb.FStar_Syntax_Syntax.lbtyp t_norm in
                                    match uu____11752 with
                                    | (tok,decl,env2) ->
                                        let uu____11785 =
                                          let uu____11792 =
                                            let uu____11798 =
                                              FStar_Util.right
                                                lb.FStar_Syntax_Syntax.lbname in
                                            (uu____11798, tok) in
                                          uu____11792 :: toks in
                                        (uu____11785, (t_norm :: typs), (decl
                                          :: decls), env2))))
                         ([], [], [], env)) in
                  match uu____11657 with
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
                        | uu____11900 ->
                            if curry
                            then
                              (match ftok with
                               | Some ftok1 -> mk_Apply ftok1 vars
                               | None  ->
                                   let uu____11905 =
                                     FStar_SMTEncoding_Util.mkFreeV
                                       (f, FStar_SMTEncoding_Term.Term_sort) in
                                   mk_Apply uu____11905 vars)
                            else
                              (let uu____11907 =
                                 let uu____11911 =
                                   FStar_List.map
                                     FStar_SMTEncoding_Util.mkFreeV vars in
                                 (f, uu____11911) in
                               FStar_SMTEncoding_Util.mkApp uu____11907) in
                      let uu____11916 =
                        (FStar_All.pipe_right quals
                           (FStar_Util.for_some
                              (fun uu___116_11918  ->
                                 match uu___116_11918 with
                                 | FStar_Syntax_Syntax.HasMaskedEffect  ->
                                     true
                                 | uu____11919 -> false)))
                          ||
                          (FStar_All.pipe_right typs1
                             (FStar_Util.for_some
                                (fun t  ->
                                   let uu____11922 =
                                     (FStar_Syntax_Util.is_pure_or_ghost_function
                                        t)
                                       ||
                                       (FStar_TypeChecker_Env.is_reifiable_function
                                          env1.tcenv t) in
                                   FStar_All.pipe_left Prims.op_Negation
                                     uu____11922))) in
                      if uu____11916
                      then (decls1, env1)
                      else
                        if Prims.op_Negation is_rec
                        then
                          (match (bindings, typs1, toks1) with
                           | ({ FStar_Syntax_Syntax.lbname = uu____11942;
                                FStar_Syntax_Syntax.lbunivs = uvs;
                                FStar_Syntax_Syntax.lbtyp = uu____11944;
                                FStar_Syntax_Syntax.lbeff = uu____11945;
                                FStar_Syntax_Syntax.lbdef = e;_}::[],t_norm::[],
                              (flid_fv,(f,ftok))::[]) ->
                               let flid =
                                 (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                               let uu____11986 =
                                 let uu____11990 =
                                   FStar_TypeChecker_Env.open_universes_in
                                     env1.tcenv uvs [e; t_norm] in
                                 match uu____11990 with
                                 | (tcenv',uu____12001,e_t) ->
                                     let uu____12005 =
                                       match e_t with
                                       | e1::t_norm1::[] -> (e1, t_norm1)
                                       | uu____12012 -> failwith "Impossible" in
                                     (match uu____12005 with
                                      | (e1,t_norm1) ->
                                          ((let uu___150_12021 = env1 in
                                            {
                                              bindings =
                                                (uu___150_12021.bindings);
                                              depth = (uu___150_12021.depth);
                                              tcenv = tcenv';
                                              warn = (uu___150_12021.warn);
                                              cache = (uu___150_12021.cache);
                                              nolabels =
                                                (uu___150_12021.nolabels);
                                              use_zfuel_name =
                                                (uu___150_12021.use_zfuel_name);
                                              encode_non_total_function_typ =
                                                (uu___150_12021.encode_non_total_function_typ);
                                              current_module_name =
                                                (uu___150_12021.current_module_name)
                                            }), e1, t_norm1)) in
                               (match uu____11986 with
                                | (env',e1,t_norm1) ->
                                    let uu____12028 =
                                      destruct_bound_function flid t_norm1 e1 in
                                    (match uu____12028 with
                                     | ((binders,body,uu____12040,uu____12041),curry)
                                         ->
                                         ((let uu____12048 =
                                             FStar_All.pipe_left
                                               (FStar_TypeChecker_Env.debug
                                                  env1.tcenv)
                                               (FStar_Options.Other
                                                  "SMTEncoding") in
                                           if uu____12048
                                           then
                                             let uu____12049 =
                                               FStar_Syntax_Print.binders_to_string
                                                 ", " binders in
                                             let uu____12050 =
                                               FStar_Syntax_Print.term_to_string
                                                 body in
                                             FStar_Util.print2
                                               "Encoding let : binders=[%s], body=%s\n"
                                               uu____12049 uu____12050
                                           else ());
                                          (let uu____12052 =
                                             encode_binders None binders env' in
                                           match uu____12052 with
                                           | (vars,guards,env'1,binder_decls,uu____12068)
                                               ->
                                               let body1 =
                                                 let uu____12076 =
                                                   FStar_TypeChecker_Env.is_reifiable_function
                                                     env'1.tcenv t_norm1 in
                                                 if uu____12076
                                                 then
                                                   FStar_TypeChecker_Util.reify_body
                                                     env'1.tcenv body
                                                 else body in
                                               let app =
                                                 mk_app1 curry f ftok vars in
                                               let uu____12079 =
                                                 let uu____12084 =
                                                   FStar_All.pipe_right quals
                                                     (FStar_List.contains
                                                        FStar_Syntax_Syntax.Logic) in
                                                 if uu____12084
                                                 then
                                                   let uu____12090 =
                                                     FStar_SMTEncoding_Term.mk_Valid
                                                       app in
                                                   let uu____12091 =
                                                     encode_formula body1
                                                       env'1 in
                                                   (uu____12090, uu____12091)
                                                 else
                                                   (let uu____12097 =
                                                      encode_term body1 env'1 in
                                                    (app, uu____12097)) in
                                               (match uu____12079 with
                                                | (app1,(body2,decls2)) ->
                                                    let eqn =
                                                      let uu____12111 =
                                                        let uu____12115 =
                                                          let uu____12116 =
                                                            let uu____12122 =
                                                              FStar_SMTEncoding_Util.mkEq
                                                                (app1, body2) in
                                                            ([[app1]], vars,
                                                              uu____12122) in
                                                          FStar_SMTEncoding_Util.mkForall
                                                            uu____12116 in
                                                        let uu____12128 =
                                                          let uu____12130 =
                                                            FStar_Util.format1
                                                              "Equation for %s"
                                                              flid.FStar_Ident.str in
                                                          Some uu____12130 in
                                                        (uu____12115,
                                                          uu____12128,
                                                          (Prims.strcat
                                                             "equation_" f)) in
                                                      FStar_SMTEncoding_Util.mkAssume
                                                        uu____12111 in
                                                    let uu____12132 =
                                                      let uu____12134 =
                                                        let uu____12136 =
                                                          let uu____12138 =
                                                            let uu____12140 =
                                                              primitive_type_axioms
                                                                env1.tcenv
                                                                flid f app1 in
                                                            FStar_List.append
                                                              [eqn]
                                                              uu____12140 in
                                                          FStar_List.append
                                                            decls2
                                                            uu____12138 in
                                                        FStar_List.append
                                                          binder_decls
                                                          uu____12136 in
                                                      FStar_List.append
                                                        decls1 uu____12134 in
                                                    (uu____12132, env1))))))
                           | uu____12143 -> failwith "Impossible")
                        else
                          (let fuel =
                             let uu____12162 = varops.fresh "fuel" in
                             (uu____12162, FStar_SMTEncoding_Term.Fuel_sort) in
                           let fuel_tm = FStar_SMTEncoding_Util.mkFreeV fuel in
                           let env0 = env1 in
                           let uu____12165 =
                             FStar_All.pipe_right toks1
                               (FStar_List.fold_left
                                  (fun uu____12204  ->
                                     fun uu____12205  ->
                                       match (uu____12204, uu____12205) with
                                       | ((gtoks,env2),(flid_fv,(f,ftok))) ->
                                           let flid =
                                             (flid_fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
                                           let g =
                                             let uu____12287 =
                                               FStar_Ident.lid_add_suffix
                                                 flid "fuel_instrumented" in
                                             varops.new_fvar uu____12287 in
                                           let gtok =
                                             let uu____12289 =
                                               FStar_Ident.lid_add_suffix
                                                 flid
                                                 "fuel_instrumented_token" in
                                             varops.new_fvar uu____12289 in
                                           let env3 =
                                             let uu____12291 =
                                               let uu____12293 =
                                                 FStar_SMTEncoding_Util.mkApp
                                                   (g, [fuel_tm]) in
                                               FStar_All.pipe_left
                                                 (fun _0_36  -> Some _0_36)
                                                 uu____12293 in
                                             push_free_var env2 flid gtok
                                               uu____12291 in
                                           (((flid, f, ftok, g, gtok) ::
                                             gtoks), env3)) ([], env1)) in
                           match uu____12165 with
                           | (gtoks,env2) ->
                               let gtoks1 = FStar_List.rev gtoks in
                               let encode_one_binding env01 uu____12379
                                 t_norm uu____12381 =
                                 match (uu____12379, uu____12381) with
                                 | ((flid,f,ftok,g,gtok),{
                                                           FStar_Syntax_Syntax.lbname
                                                             = lbn;
                                                           FStar_Syntax_Syntax.lbunivs
                                                             = uvs;
                                                           FStar_Syntax_Syntax.lbtyp
                                                             = uu____12408;
                                                           FStar_Syntax_Syntax.lbeff
                                                             = uu____12409;
                                                           FStar_Syntax_Syntax.lbdef
                                                             = e;_})
                                     ->
                                     let uu____12426 =
                                       let uu____12430 =
                                         FStar_TypeChecker_Env.open_universes_in
                                           env2.tcenv uvs [e; t_norm] in
                                       match uu____12430 with
                                       | (tcenv',uu____12445,e_t) ->
                                           let uu____12449 =
                                             match e_t with
                                             | e1::t_norm1::[] ->
                                                 (e1, t_norm1)
                                             | uu____12456 ->
                                                 failwith "Impossible" in
                                           (match uu____12449 with
                                            | (e1,t_norm1) ->
                                                ((let uu___151_12465 = env2 in
                                                  {
                                                    bindings =
                                                      (uu___151_12465.bindings);
                                                    depth =
                                                      (uu___151_12465.depth);
                                                    tcenv = tcenv';
                                                    warn =
                                                      (uu___151_12465.warn);
                                                    cache =
                                                      (uu___151_12465.cache);
                                                    nolabels =
                                                      (uu___151_12465.nolabels);
                                                    use_zfuel_name =
                                                      (uu___151_12465.use_zfuel_name);
                                                    encode_non_total_function_typ
                                                      =
                                                      (uu___151_12465.encode_non_total_function_typ);
                                                    current_module_name =
                                                      (uu___151_12465.current_module_name)
                                                  }), e1, t_norm1)) in
                                     (match uu____12426 with
                                      | (env',e1,t_norm1) ->
                                          ((let uu____12475 =
                                              FStar_All.pipe_left
                                                (FStar_TypeChecker_Env.debug
                                                   env01.tcenv)
                                                (FStar_Options.Other
                                                   "SMTEncoding") in
                                            if uu____12475
                                            then
                                              let uu____12476 =
                                                FStar_Syntax_Print.lbname_to_string
                                                  lbn in
                                              let uu____12477 =
                                                FStar_Syntax_Print.term_to_string
                                                  t_norm1 in
                                              let uu____12478 =
                                                FStar_Syntax_Print.term_to_string
                                                  e1 in
                                              FStar_Util.print3
                                                "Encoding let rec %s : %s = %s\n"
                                                uu____12476 uu____12477
                                                uu____12478
                                            else ());
                                           (let uu____12480 =
                                              destruct_bound_function flid
                                                t_norm1 e1 in
                                            match uu____12480 with
                                            | ((binders,body,formals,tres),curry)
                                                ->
                                                ((let uu____12502 =
                                                    FStar_All.pipe_left
                                                      (FStar_TypeChecker_Env.debug
                                                         env01.tcenv)
                                                      (FStar_Options.Other
                                                         "SMTEncoding") in
                                                  if uu____12502
                                                  then
                                                    let uu____12503 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " binders in
                                                    let uu____12504 =
                                                      FStar_Syntax_Print.term_to_string
                                                        body in
                                                    let uu____12505 =
                                                      FStar_Syntax_Print.binders_to_string
                                                        ", " formals in
                                                    let uu____12506 =
                                                      FStar_Syntax_Print.term_to_string
                                                        tres in
                                                    FStar_Util.print4
                                                      "Encoding let rec: binders=[%s], body=%s, formals=[%s], tres=%s\n"
                                                      uu____12503 uu____12504
                                                      uu____12505 uu____12506
                                                  else ());
                                                 if curry
                                                 then
                                                   failwith
                                                     "Unexpected type of let rec in SMT Encoding; expected it to be annotated with an arrow type"
                                                 else ();
                                                 (let uu____12510 =
                                                    encode_binders None
                                                      binders env' in
                                                  match uu____12510 with
                                                  | (vars,guards,env'1,binder_decls,uu____12528)
                                                      ->
                                                      let decl_g =
                                                        let uu____12536 =
                                                          let uu____12542 =
                                                            let uu____12544 =
                                                              FStar_List.map
                                                                FStar_Pervasives.snd
                                                                vars in
                                                            FStar_SMTEncoding_Term.Fuel_sort
                                                              :: uu____12544 in
                                                          (g, uu____12542,
                                                            FStar_SMTEncoding_Term.Term_sort,
                                                            (Some
                                                               "Fuel-instrumented function name")) in
                                                        FStar_SMTEncoding_Term.DeclFun
                                                          uu____12536 in
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
                                                        let uu____12559 =
                                                          let uu____12563 =
                                                            FStar_List.map
                                                              FStar_SMTEncoding_Util.mkFreeV
                                                              vars in
                                                          (f, uu____12563) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12559 in
                                                      let gsapp =
                                                        let uu____12569 =
                                                          let uu____12573 =
                                                            let uu____12575 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("SFuel",
                                                                  [fuel_tm]) in
                                                            uu____12575 ::
                                                              vars_tm in
                                                          (g, uu____12573) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12569 in
                                                      let gmax =
                                                        let uu____12579 =
                                                          let uu____12583 =
                                                            let uu____12585 =
                                                              FStar_SMTEncoding_Util.mkApp
                                                                ("MaxFuel",
                                                                  []) in
                                                            uu____12585 ::
                                                              vars_tm in
                                                          (g, uu____12583) in
                                                        FStar_SMTEncoding_Util.mkApp
                                                          uu____12579 in
                                                      let body1 =
                                                        let uu____12589 =
                                                          FStar_TypeChecker_Env.is_reifiable_function
                                                            env'1.tcenv
                                                            t_norm1 in
                                                        if uu____12589
                                                        then
                                                          FStar_TypeChecker_Util.reify_body
                                                            env'1.tcenv body
                                                        else body in
                                                      let uu____12591 =
                                                        encode_term body1
                                                          env'1 in
                                                      (match uu____12591 with
                                                       | (body_tm,decls2) ->
                                                           let eqn_g =
                                                             let uu____12602
                                                               =
                                                               let uu____12606
                                                                 =
                                                                 let uu____12607
                                                                   =
                                                                   let uu____12615
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
                                                                    uu____12615) in
                                                                 FStar_SMTEncoding_Util.mkForall'
                                                                   uu____12607 in
                                                               let uu____12626
                                                                 =
                                                                 let uu____12628
                                                                   =
                                                                   FStar_Util.format1
                                                                    "Equation for fuel-instrumented recursive function: %s"
                                                                    flid.FStar_Ident.str in
                                                                 Some
                                                                   uu____12628 in
                                                               (uu____12606,
                                                                 uu____12626,
                                                                 (Prims.strcat
                                                                    "equation_with_fuel_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12602 in
                                                           let eqn_f =
                                                             let uu____12631
                                                               =
                                                               let uu____12635
                                                                 =
                                                                 let uu____12636
                                                                   =
                                                                   let uu____12642
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    gmax) in
                                                                   ([[app]],
                                                                    vars,
                                                                    uu____12642) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12636 in
                                                               (uu____12635,
                                                                 (Some
                                                                    "Correspondence of recursive function to instrumented version"),
                                                                 (Prims.strcat
                                                                    "@fuel_correspondence_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12631 in
                                                           let eqn_g' =
                                                             let uu____12650
                                                               =
                                                               let uu____12654
                                                                 =
                                                                 let uu____12655
                                                                   =
                                                                   let uu____12661
                                                                    =
                                                                    let uu____12662
                                                                    =
                                                                    let uu____12665
                                                                    =
                                                                    let uu____12666
                                                                    =
                                                                    let uu____12670
                                                                    =
                                                                    let uu____12672
                                                                    =
                                                                    FStar_SMTEncoding_Term.n_fuel
                                                                    (Prims.parse_int
                                                                    "0") in
                                                                    uu____12672
                                                                    ::
                                                                    vars_tm in
                                                                    (g,
                                                                    uu____12670) in
                                                                    FStar_SMTEncoding_Util.mkApp
                                                                    uu____12666 in
                                                                    (gsapp,
                                                                    uu____12665) in
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    uu____12662 in
                                                                   ([[gsapp]],
                                                                    (fuel ::
                                                                    vars),
                                                                    uu____12661) in
                                                                 FStar_SMTEncoding_Util.mkForall
                                                                   uu____12655 in
                                                               (uu____12654,
                                                                 (Some
                                                                    "Fuel irrelevance"),
                                                                 (Prims.strcat
                                                                    "@fuel_irrelevance_"
                                                                    g)) in
                                                             FStar_SMTEncoding_Util.mkAssume
                                                               uu____12650 in
                                                           let uu____12684 =
                                                             let uu____12689
                                                               =
                                                               encode_binders
                                                                 None formals
                                                                 env02 in
                                                             match uu____12689
                                                             with
                                                             | (vars1,v_guards,env3,binder_decls1,uu____12706)
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
                                                                    let uu____12721
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    (gtok,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    mk_Apply
                                                                    uu____12721
                                                                    (fuel ::
                                                                    vars1) in
                                                                   let uu____12724
                                                                    =
                                                                    let uu____12728
                                                                    =
                                                                    let uu____12729
                                                                    =
                                                                    let uu____12735
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (tok_app,
                                                                    gapp) in
                                                                    ([
                                                                    [tok_app]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12735) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12729 in
                                                                    (uu____12728,
                                                                    (Some
                                                                    "Fuel token correspondence"),
                                                                    (Prims.strcat
                                                                    "fuel_token_correspondence_"
                                                                    gtok)) in
                                                                   FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12724 in
                                                                 let uu____12746
                                                                   =
                                                                   let uu____12750
                                                                    =
                                                                    encode_term_pred
                                                                    None tres
                                                                    env3 gapp in
                                                                   match uu____12750
                                                                   with
                                                                   | 
                                                                   (g_typing,d3)
                                                                    ->
                                                                    let uu____12758
                                                                    =
                                                                    let uu____12760
                                                                    =
                                                                    let uu____12761
                                                                    =
                                                                    let uu____12765
                                                                    =
                                                                    let uu____12766
                                                                    =
                                                                    let uu____12772
                                                                    =
                                                                    let uu____12773
                                                                    =
                                                                    let uu____12776
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    v_guards in
                                                                    (uu____12776,
                                                                    g_typing) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____12773 in
                                                                    ([[gapp]],
                                                                    (fuel ::
                                                                    vars1),
                                                                    uu____12772) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____12766 in
                                                                    (uu____12765,
                                                                    (Some
                                                                    "Typing correspondence of token to term"),
                                                                    (Prims.strcat
                                                                    "token_correspondence_"
                                                                    g)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____12761 in
                                                                    [uu____12760] in
                                                                    (d3,
                                                                    uu____12758) in
                                                                 (match uu____12746
                                                                  with
                                                                  | (aux_decls,typing_corr)
                                                                    ->
                                                                    ((FStar_List.append
                                                                    binder_decls1
                                                                    aux_decls),
                                                                    (FStar_List.append
                                                                    typing_corr
                                                                    [tok_corr]))) in
                                                           (match uu____12684
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
                               let uu____12811 =
                                 let uu____12818 =
                                   FStar_List.zip3 gtoks1 typs1 bindings in
                                 FStar_List.fold_left
                                   (fun uu____12854  ->
                                      fun uu____12855  ->
                                        match (uu____12854, uu____12855) with
                                        | ((decls2,eqns,env01),(gtok,ty,lb))
                                            ->
                                            let uu____12941 =
                                              encode_one_binding env01 gtok
                                                ty lb in
                                            (match uu____12941 with
                                             | (decls',eqns',env02) ->
                                                 ((decls' :: decls2),
                                                   (FStar_List.append eqns'
                                                      eqns), env02)))
                                   ([decls1], [], env0) uu____12818 in
                               (match uu____12811 with
                                | (decls2,eqns,env01) ->
                                    let uu____12981 =
                                      let isDeclFun uu___117_12989 =
                                        match uu___117_12989 with
                                        | FStar_SMTEncoding_Term.DeclFun
                                            uu____12990 -> true
                                        | uu____12996 -> false in
                                      let uu____12997 =
                                        FStar_All.pipe_right decls2
                                          FStar_List.flatten in
                                      FStar_All.pipe_right uu____12997
                                        (FStar_List.partition isDeclFun) in
                                    (match uu____12981 with
                                     | (prefix_decls,rest) ->
                                         let eqns1 = FStar_List.rev eqns in
                                         ((FStar_List.append prefix_decls
                                             (FStar_List.append rest eqns1)),
                                           env01)))))
             with
             | Let_rec_unencodeable  ->
                 let msg =
                   let uu____13024 =
                     FStar_All.pipe_right bindings
                       (FStar_List.map
                          (fun lb  ->
                             FStar_Syntax_Print.lbname_to_string
                               lb.FStar_Syntax_Syntax.lbname)) in
                   FStar_All.pipe_right uu____13024
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
        let uu____13057 = FStar_Syntax_Util.lid_of_sigelt se in
        match uu____13057 with | None  -> "" | Some l -> l.FStar_Ident.str in
      let uu____13060 = encode_sigelt' env se in
      match uu____13060 with
      | (g,env1) ->
          let g1 =
            match g with
            | [] ->
                let uu____13070 =
                  let uu____13071 = FStar_Util.format1 "<Skipped %s/>" nm in
                  FStar_SMTEncoding_Term.Caption uu____13071 in
                [uu____13070]
            | uu____13072 ->
                let uu____13073 =
                  let uu____13075 =
                    let uu____13076 =
                      FStar_Util.format1 "<Start encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13076 in
                  uu____13075 :: g in
                let uu____13077 =
                  let uu____13079 =
                    let uu____13080 =
                      FStar_Util.format1 "</end encoding %s>" nm in
                    FStar_SMTEncoding_Term.Caption uu____13080 in
                  [uu____13079] in
                FStar_List.append uu____13073 uu____13077 in
          (g1, env1)
and encode_sigelt':
  env_t ->
    FStar_Syntax_Syntax.sigelt -> (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun se  ->
      match se.FStar_Syntax_Syntax.sigel with
      | FStar_Syntax_Syntax.Sig_new_effect_for_free uu____13088 ->
          failwith "impossible -- removed by tc.fs"
      | FStar_Syntax_Syntax.Sig_pragma uu____13091 -> ([], env)
      | FStar_Syntax_Syntax.Sig_main uu____13093 -> ([], env)
      | FStar_Syntax_Syntax.Sig_effect_abbrev uu____13095 -> ([], env)
      | FStar_Syntax_Syntax.Sig_sub_effect uu____13103 -> ([], env)
      | FStar_Syntax_Syntax.Sig_new_effect ed ->
          let uu____13106 =
            let uu____13107 =
              FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
                (FStar_List.contains FStar_Syntax_Syntax.Reifiable) in
            FStar_All.pipe_right uu____13107 Prims.op_Negation in
          if uu____13106
          then ([], env)
          else
            (let close_effect_params tm =
               match ed.FStar_Syntax_Syntax.binders with
               | [] -> tm
               | uu____13127 ->
                   let uu____13128 =
                     let uu____13131 =
                       let uu____13132 =
                         let uu____13147 =
                           FStar_All.pipe_left (fun _0_37  -> Some _0_37)
                             (FStar_Util.Inr
                                (FStar_Syntax_Const.effect_Tot_lid,
                                  [FStar_Syntax_Syntax.TOTAL])) in
                         ((ed.FStar_Syntax_Syntax.binders), tm, uu____13147) in
                       FStar_Syntax_Syntax.Tm_abs uu____13132 in
                     FStar_Syntax_Syntax.mk uu____13131 in
                   uu____13128 None tm.FStar_Syntax_Syntax.pos in
             let encode_action env1 a =
               let uu____13200 =
                 new_term_constant_and_tok_from_lid env1
                   a.FStar_Syntax_Syntax.action_name in
               match uu____13200 with
               | (aname,atok,env2) ->
                   let uu____13210 =
                     FStar_Syntax_Util.arrow_formals_comp
                       a.FStar_Syntax_Syntax.action_typ in
                   (match uu____13210 with
                    | (formals,uu____13220) ->
                        let uu____13227 =
                          let uu____13230 =
                            close_effect_params
                              a.FStar_Syntax_Syntax.action_defn in
                          encode_term uu____13230 env2 in
                        (match uu____13227 with
                         | (tm,decls) ->
                             let a_decls =
                               let uu____13238 =
                                 let uu____13239 =
                                   let uu____13245 =
                                     FStar_All.pipe_right formals
                                       (FStar_List.map
                                          (fun uu____13253  ->
                                             FStar_SMTEncoding_Term.Term_sort)) in
                                   (aname, uu____13245,
                                     FStar_SMTEncoding_Term.Term_sort,
                                     (Some "Action")) in
                                 FStar_SMTEncoding_Term.DeclFun uu____13239 in
                               [uu____13238;
                               FStar_SMTEncoding_Term.DeclFun
                                 (atok, [], FStar_SMTEncoding_Term.Term_sort,
                                   (Some "Action token"))] in
                             let uu____13260 =
                               let aux uu____13289 uu____13290 =
                                 match (uu____13289, uu____13290) with
                                 | ((bv,uu____13317),(env3,acc_sorts,acc)) ->
                                     let uu____13338 = gen_term_var env3 bv in
                                     (match uu____13338 with
                                      | (xxsym,xx,env4) ->
                                          (env4,
                                            ((xxsym,
                                               FStar_SMTEncoding_Term.Term_sort)
                                            :: acc_sorts), (xx :: acc))) in
                               FStar_List.fold_right aux formals
                                 (env2, [], []) in
                             (match uu____13260 with
                              | (uu____13376,xs_sorts,xs) ->
                                  let app =
                                    FStar_SMTEncoding_Util.mkApp (aname, xs) in
                                  let a_eq =
                                    let uu____13390 =
                                      let uu____13394 =
                                        let uu____13395 =
                                          let uu____13401 =
                                            let uu____13402 =
                                              let uu____13405 =
                                                mk_Apply tm xs_sorts in
                                              (app, uu____13405) in
                                            FStar_SMTEncoding_Util.mkEq
                                              uu____13402 in
                                          ([[app]], xs_sorts, uu____13401) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13395 in
                                      (uu____13394, (Some "Action equality"),
                                        (Prims.strcat aname "_equality")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13390 in
                                  let tok_correspondence =
                                    let tok_term =
                                      FStar_SMTEncoding_Util.mkFreeV
                                        (atok,
                                          FStar_SMTEncoding_Term.Term_sort) in
                                    let tok_app = mk_Apply tok_term xs_sorts in
                                    let uu____13417 =
                                      let uu____13421 =
                                        let uu____13422 =
                                          let uu____13428 =
                                            FStar_SMTEncoding_Util.mkEq
                                              (tok_app, app) in
                                          ([[tok_app]], xs_sorts,
                                            uu____13428) in
                                        FStar_SMTEncoding_Util.mkForall
                                          uu____13422 in
                                      (uu____13421,
                                        (Some "Action token correspondence"),
                                        (Prims.strcat aname
                                           "_token_correspondence")) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____13417 in
                                  (env2,
                                    (FStar_List.append decls
                                       (FStar_List.append a_decls
                                          [a_eq; tok_correspondence])))))) in
             let uu____13438 =
               FStar_Util.fold_map encode_action env
                 ed.FStar_Syntax_Syntax.actions in
             match uu____13438 with
             | (env1,decls2) -> ((FStar_List.flatten decls2), env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13454,uu____13455)
          when FStar_Ident.lid_equals lid FStar_Syntax_Const.precedes_lid ->
          let uu____13456 = new_term_constant_and_tok_from_lid env lid in
          (match uu____13456 with | (tname,ttok,env1) -> ([], env1))
      | FStar_Syntax_Syntax.Sig_declare_typ (lid,uu____13467,t) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let will_encode_definition =
            let uu____13472 =
              FStar_All.pipe_right quals
                (FStar_Util.for_some
                   (fun uu___118_13474  ->
                      match uu___118_13474 with
                      | FStar_Syntax_Syntax.Assumption  -> true
                      | FStar_Syntax_Syntax.Projector uu____13475 -> true
                      | FStar_Syntax_Syntax.Discriminator uu____13478 -> true
                      | FStar_Syntax_Syntax.Irreducible  -> true
                      | uu____13479 -> false)) in
            Prims.op_Negation uu____13472 in
          if will_encode_definition
          then ([], env)
          else
            (let fv =
               FStar_Syntax_Syntax.lid_as_fv lid
                 FStar_Syntax_Syntax.Delta_constant None in
             let uu____13485 = encode_top_level_val env fv t quals in
             match uu____13485 with
             | (decls,env1) ->
                 let tname = lid.FStar_Ident.str in
                 let tsym =
                   FStar_SMTEncoding_Util.mkFreeV
                     (tname, FStar_SMTEncoding_Term.Term_sort) in
                 let uu____13497 =
                   let uu____13499 =
                     primitive_type_axioms env1.tcenv lid tname tsym in
                   FStar_List.append decls uu____13499 in
                 (uu____13497, env1))
      | FStar_Syntax_Syntax.Sig_assume (l,us,f) ->
          let uu____13505 = FStar_Syntax_Subst.open_univ_vars us f in
          (match uu____13505 with
           | (uu____13510,f1) ->
               let uu____13512 = encode_formula f1 env in
               (match uu____13512 with
                | (f2,decls) ->
                    let g =
                      let uu____13521 =
                        let uu____13522 =
                          let uu____13526 =
                            let uu____13528 =
                              let uu____13529 =
                                FStar_Syntax_Print.lid_to_string l in
                              FStar_Util.format1 "Assumption: %s" uu____13529 in
                            Some uu____13528 in
                          let uu____13530 =
                            varops.mk_unique
                              (Prims.strcat "assumption_" l.FStar_Ident.str) in
                          (f2, uu____13526, uu____13530) in
                        FStar_SMTEncoding_Util.mkAssume uu____13522 in
                      [uu____13521] in
                    ((FStar_List.append decls g), env)))
      | FStar_Syntax_Syntax.Sig_let (lbs,uu____13534,uu____13535) when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_List.contains FStar_Syntax_Syntax.Irreducible)
          ->
          let uu____13541 =
            FStar_Util.fold_map
              (fun env1  ->
                 fun lb  ->
                   let lid =
                     let uu____13548 =
                       let uu____13553 =
                         FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
                       uu____13553.FStar_Syntax_Syntax.fv_name in
                     uu____13548.FStar_Syntax_Syntax.v in
                   let uu____13557 =
                     let uu____13558 =
                       FStar_TypeChecker_Env.try_lookup_val_decl env1.tcenv
                         lid in
                     FStar_All.pipe_left FStar_Option.isNone uu____13558 in
                   if uu____13557
                   then
                     let val_decl =
                       let uu___152_13573 = se in
                       {
                         FStar_Syntax_Syntax.sigel =
                           (FStar_Syntax_Syntax.Sig_declare_typ
                              (lid, (lb.FStar_Syntax_Syntax.lbunivs),
                                (lb.FStar_Syntax_Syntax.lbtyp)));
                         FStar_Syntax_Syntax.sigrng =
                           (uu___152_13573.FStar_Syntax_Syntax.sigrng);
                         FStar_Syntax_Syntax.sigquals =
                           (uu___152_13573.FStar_Syntax_Syntax.sigquals);
                         FStar_Syntax_Syntax.sigmeta =
                           (uu___152_13573.FStar_Syntax_Syntax.sigmeta)
                       } in
                     let uu____13577 = encode_sigelt' env1 val_decl in
                     match uu____13577 with | (decls,env2) -> (env2, decls)
                   else (env1, [])) env (snd lbs) in
          (match uu____13541 with
           | (env1,decls) -> ((FStar_List.flatten decls), env1))
      | FStar_Syntax_Syntax.Sig_let
          ((uu____13594,{ FStar_Syntax_Syntax.lbname = FStar_Util.Inr b2t1;
                          FStar_Syntax_Syntax.lbunivs = uu____13596;
                          FStar_Syntax_Syntax.lbtyp = uu____13597;
                          FStar_Syntax_Syntax.lbeff = uu____13598;
                          FStar_Syntax_Syntax.lbdef = uu____13599;_}::[]),uu____13600,uu____13601)
          when FStar_Syntax_Syntax.fv_eq_lid b2t1 FStar_Syntax_Const.b2t_lid
          ->
          let uu____13615 =
            new_term_constant_and_tok_from_lid env
              (b2t1.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          (match uu____13615 with
           | (tname,ttok,env1) ->
               let xx = ("x", FStar_SMTEncoding_Term.Term_sort) in
               let x = FStar_SMTEncoding_Util.mkFreeV xx in
               let b2t_x = FStar_SMTEncoding_Util.mkApp ("Prims.b2t", [x]) in
               let valid_b2t_x =
                 FStar_SMTEncoding_Util.mkApp ("Valid", [b2t_x]) in
               let decls =
                 let uu____13638 =
                   let uu____13640 =
                     let uu____13641 =
                       let uu____13645 =
                         let uu____13646 =
                           let uu____13652 =
                             let uu____13653 =
                               let uu____13656 =
                                 FStar_SMTEncoding_Util.mkApp
                                   ("BoxBool_proj_0", [x]) in
                               (valid_b2t_x, uu____13656) in
                             FStar_SMTEncoding_Util.mkEq uu____13653 in
                           ([[b2t_x]], [xx], uu____13652) in
                         FStar_SMTEncoding_Util.mkForall uu____13646 in
                       (uu____13645, (Some "b2t def"), "b2t_def") in
                     FStar_SMTEncoding_Util.mkAssume uu____13641 in
                   [uu____13640] in
                 (FStar_SMTEncoding_Term.DeclFun
                    (tname, [FStar_SMTEncoding_Term.Term_sort],
                      FStar_SMTEncoding_Term.Term_sort, None))
                   :: uu____13638 in
               (decls, env1))
      | FStar_Syntax_Syntax.Sig_let (uu____13673,uu____13674,uu____13675)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___119_13681  ->
                  match uu___119_13681 with
                  | FStar_Syntax_Syntax.Discriminator uu____13682 -> true
                  | uu____13683 -> false))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let (uu____13685,lids,uu____13687) when
          (FStar_All.pipe_right lids
             (FStar_Util.for_some
                (fun l  ->
                   let uu____13694 =
                     let uu____13695 = FStar_List.hd l.FStar_Ident.ns in
                     uu____13695.FStar_Ident.idText in
                   uu____13694 = "Prims")))
            &&
            (FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
               (FStar_Util.for_some
                  (fun uu___120_13697  ->
                     match uu___120_13697 with
                     | FStar_Syntax_Syntax.Unfold_for_unification_and_vcgen 
                         -> true
                     | uu____13698 -> false)))
          -> ([], env)
      | FStar_Syntax_Syntax.Sig_let ((false ,lb::[]),uu____13701,uu____13702)
          when
          FStar_All.pipe_right se.FStar_Syntax_Syntax.sigquals
            (FStar_Util.for_some
               (fun uu___121_13712  ->
                  match uu___121_13712 with
                  | FStar_Syntax_Syntax.Projector uu____13713 -> true
                  | uu____13716 -> false))
          ->
          let fv = FStar_Util.right lb.FStar_Syntax_Syntax.lbname in
          let l = (fv.FStar_Syntax_Syntax.fv_name).FStar_Syntax_Syntax.v in
          let uu____13723 = try_lookup_free_var env l in
          (match uu____13723 with
           | Some uu____13727 -> ([], env)
           | None  ->
               let se1 =
                 let uu___153_13730 = se in
                 {
                   FStar_Syntax_Syntax.sigel =
                     (FStar_Syntax_Syntax.Sig_declare_typ
                        (l, (lb.FStar_Syntax_Syntax.lbunivs),
                          (lb.FStar_Syntax_Syntax.lbtyp)));
                   FStar_Syntax_Syntax.sigrng = (FStar_Ident.range_of_lid l);
                   FStar_Syntax_Syntax.sigquals =
                     (uu___153_13730.FStar_Syntax_Syntax.sigquals);
                   FStar_Syntax_Syntax.sigmeta =
                     (uu___153_13730.FStar_Syntax_Syntax.sigmeta)
                 } in
               encode_sigelt env se1)
      | FStar_Syntax_Syntax.Sig_let
          ((is_rec,bindings),uu____13736,uu____13737) ->
          encode_top_level_let env (is_rec, bindings)
            se.FStar_Syntax_Syntax.sigquals
      | FStar_Syntax_Syntax.Sig_bundle (ses,uu____13749) ->
          let uu____13754 = encode_sigelts env ses in
          (match uu____13754 with
           | (g,env1) ->
               let uu____13764 =
                 FStar_All.pipe_right g
                   (FStar_List.partition
                      (fun uu___122_13774  ->
                         match uu___122_13774 with
                         | FStar_SMTEncoding_Term.Assume
                             {
                               FStar_SMTEncoding_Term.assumption_term =
                                 uu____13775;
                               FStar_SMTEncoding_Term.assumption_caption =
                                 Some "inversion axiom";
                               FStar_SMTEncoding_Term.assumption_name =
                                 uu____13776;
                               FStar_SMTEncoding_Term.assumption_fact_ids =
                                 uu____13777;_}
                             -> false
                         | uu____13779 -> true)) in
               (match uu____13764 with
                | (g',inversions) ->
                    let uu____13788 =
                      FStar_All.pipe_right g'
                        (FStar_List.partition
                           (fun uu___123_13798  ->
                              match uu___123_13798 with
                              | FStar_SMTEncoding_Term.DeclFun uu____13799 ->
                                  true
                              | uu____13805 -> false)) in
                    (match uu____13788 with
                     | (decls,rest) ->
                         ((FStar_List.append decls
                             (FStar_List.append rest inversions)), env1))))
      | FStar_Syntax_Syntax.Sig_inductive_typ
          (t,uu____13816,tps,k,uu____13819,datas) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let is_logical =
            FStar_All.pipe_right quals
              (FStar_Util.for_some
                 (fun uu___124_13829  ->
                    match uu___124_13829 with
                    | FStar_Syntax_Syntax.Logic  -> true
                    | FStar_Syntax_Syntax.Assumption  -> true
                    | uu____13830 -> false)) in
          let constructor_or_logic_type_decl c =
            if is_logical
            then
              let uu____13837 = c in
              match uu____13837 with
              | (name,args,uu____13841,uu____13842,uu____13843) ->
                  let uu____13846 =
                    let uu____13847 =
                      let uu____13853 =
                        FStar_All.pipe_right args
                          (FStar_List.map
                             (fun uu____13860  ->
                                match uu____13860 with
                                | (uu____13864,sort,uu____13866) -> sort)) in
                      (name, uu____13853, FStar_SMTEncoding_Term.Term_sort,
                        None) in
                    FStar_SMTEncoding_Term.DeclFun uu____13847 in
                  [uu____13846]
            else FStar_SMTEncoding_Term.constructor_to_decl c in
          let inversion_axioms tapp vars =
            let uu____13884 =
              FStar_All.pipe_right datas
                (FStar_Util.for_some
                   (fun l  ->
                      let uu____13887 =
                        FStar_TypeChecker_Env.try_lookup_lid env.tcenv l in
                      FStar_All.pipe_right uu____13887 FStar_Option.isNone)) in
            if uu____13884
            then []
            else
              (let uu____13904 =
                 fresh_fvar "x" FStar_SMTEncoding_Term.Term_sort in
               match uu____13904 with
               | (xxsym,xx) ->
                   let uu____13910 =
                     FStar_All.pipe_right datas
                       (FStar_List.fold_left
                          (fun uu____13921  ->
                             fun l  ->
                               match uu____13921 with
                               | (out,decls) ->
                                   let uu____13933 =
                                     FStar_TypeChecker_Env.lookup_datacon
                                       env.tcenv l in
                                   (match uu____13933 with
                                    | (uu____13939,data_t) ->
                                        let uu____13941 =
                                          FStar_Syntax_Util.arrow_formals
                                            data_t in
                                        (match uu____13941 with
                                         | (args,res) ->
                                             let indices =
                                               let uu____13970 =
                                                 let uu____13971 =
                                                   FStar_Syntax_Subst.compress
                                                     res in
                                                 uu____13971.FStar_Syntax_Syntax.n in
                                               match uu____13970 with
                                               | FStar_Syntax_Syntax.Tm_app
                                                   (uu____13979,indices) ->
                                                   indices
                                               | uu____13995 -> [] in
                                             let env1 =
                                               FStar_All.pipe_right args
                                                 (FStar_List.fold_left
                                                    (fun env1  ->
                                                       fun uu____14007  ->
                                                         match uu____14007
                                                         with
                                                         | (x,uu____14011) ->
                                                             let uu____14012
                                                               =
                                                               let uu____14013
                                                                 =
                                                                 let uu____14017
                                                                   =
                                                                   mk_term_projector_name
                                                                    l x in
                                                                 (uu____14017,
                                                                   [xx]) in
                                                               FStar_SMTEncoding_Util.mkApp
                                                                 uu____14013 in
                                                             push_term_var
                                                               env1 x
                                                               uu____14012)
                                                    env) in
                                             let uu____14019 =
                                               encode_args indices env1 in
                                             (match uu____14019 with
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
                                                      let uu____14039 =
                                                        FStar_List.map2
                                                          (fun v1  ->
                                                             fun a  ->
                                                               let uu____14047
                                                                 =
                                                                 let uu____14050
                                                                   =
                                                                   FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                 (uu____14050,
                                                                   a) in
                                                               FStar_SMTEncoding_Util.mkEq
                                                                 uu____14047)
                                                          vars indices1 in
                                                      FStar_All.pipe_right
                                                        uu____14039
                                                        FStar_SMTEncoding_Util.mk_and_l in
                                                    let uu____14052 =
                                                      let uu____14053 =
                                                        let uu____14056 =
                                                          let uu____14057 =
                                                            let uu____14060 =
                                                              mk_data_tester
                                                                env1 l xx in
                                                            (uu____14060,
                                                              eqs) in
                                                          FStar_SMTEncoding_Util.mkAnd
                                                            uu____14057 in
                                                        (out, uu____14056) in
                                                      FStar_SMTEncoding_Util.mkOr
                                                        uu____14053 in
                                                    (uu____14052,
                                                      (FStar_List.append
                                                         decls decls'))))))))
                          (FStar_SMTEncoding_Util.mkFalse, [])) in
                   (match uu____13910 with
                    | (data_ax,decls) ->
                        let uu____14068 =
                          fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                        (match uu____14068 with
                         | (ffsym,ff) ->
                             let fuel_guarded_inversion =
                               let xx_has_type_sfuel =
                                 if
                                   (FStar_List.length datas) >
                                     (Prims.parse_int "1")
                                 then
                                   let uu____14079 =
                                     FStar_SMTEncoding_Util.mkApp
                                       ("SFuel", [ff]) in
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel
                                     uu____14079 xx tapp
                                 else
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                               let uu____14082 =
                                 let uu____14086 =
                                   let uu____14087 =
                                     let uu____14093 =
                                       add_fuel
                                         (ffsym,
                                           FStar_SMTEncoding_Term.Fuel_sort)
                                         ((xxsym,
                                            FStar_SMTEncoding_Term.Term_sort)
                                         :: vars) in
                                     let uu____14101 =
                                       FStar_SMTEncoding_Util.mkImp
                                         (xx_has_type_sfuel, data_ax) in
                                     ([[xx_has_type_sfuel]], uu____14093,
                                       uu____14101) in
                                   FStar_SMTEncoding_Util.mkForall
                                     uu____14087 in
                                 let uu____14109 =
                                   varops.mk_unique
                                     (Prims.strcat "fuel_guarded_inversion_"
                                        t.FStar_Ident.str) in
                                 (uu____14086, (Some "inversion axiom"),
                                   uu____14109) in
                               FStar_SMTEncoding_Util.mkAssume uu____14082 in
                             let pattern_guarded_inversion =
                               let uu____14113 =
                                 (contains_name env "Prims.inversion") &&
                                   ((FStar_List.length datas) >
                                      (Prims.parse_int "1")) in
                               if uu____14113
                               then
                                 let xx_has_type_fuel =
                                   FStar_SMTEncoding_Term.mk_HasTypeFuel ff
                                     xx tapp in
                                 let pattern_guard =
                                   FStar_SMTEncoding_Util.mkApp
                                     ("Prims.inversion", [tapp]) in
                                 let uu____14121 =
                                   let uu____14122 =
                                     let uu____14126 =
                                       let uu____14127 =
                                         let uu____14133 =
                                           add_fuel
                                             (ffsym,
                                               FStar_SMTEncoding_Term.Fuel_sort)
                                             ((xxsym,
                                                FStar_SMTEncoding_Term.Term_sort)
                                             :: vars) in
                                         let uu____14141 =
                                           FStar_SMTEncoding_Util.mkImp
                                             (xx_has_type_fuel, data_ax) in
                                         ([[xx_has_type_fuel; pattern_guard]],
                                           uu____14133, uu____14141) in
                                       FStar_SMTEncoding_Util.mkForall
                                         uu____14127 in
                                     let uu____14149 =
                                       varops.mk_unique
                                         (Prims.strcat
                                            "pattern_guarded_inversion_"
                                            t.FStar_Ident.str) in
                                     (uu____14126, (Some "inversion axiom"),
                                       uu____14149) in
                                   FStar_SMTEncoding_Util.mkAssume
                                     uu____14122 in
                                 [uu____14121]
                               else [] in
                             FStar_List.append decls
                               (FStar_List.append [fuel_guarded_inversion]
                                  pattern_guarded_inversion)))) in
          let uu____14152 =
            let uu____14160 =
              let uu____14161 = FStar_Syntax_Subst.compress k in
              uu____14161.FStar_Syntax_Syntax.n in
            match uu____14160 with
            | FStar_Syntax_Syntax.Tm_arrow (formals,kres) ->
                ((FStar_List.append tps formals),
                  (FStar_Syntax_Util.comp_result kres))
            | uu____14190 -> (tps, k) in
          (match uu____14152 with
           | (formals,res) ->
               let uu____14205 = FStar_Syntax_Subst.open_term formals res in
               (match uu____14205 with
                | (formals1,res1) ->
                    let uu____14212 = encode_binders None formals1 env in
                    (match uu____14212 with
                     | (vars,guards,env',binder_decls,uu____14227) ->
                         let uu____14234 =
                           new_term_constant_and_tok_from_lid env t in
                         (match uu____14234 with
                          | (tname,ttok,env1) ->
                              let ttok_tm =
                                FStar_SMTEncoding_Util.mkApp (ttok, []) in
                              let guard =
                                FStar_SMTEncoding_Util.mk_and_l guards in
                              let tapp =
                                let uu____14247 =
                                  let uu____14251 =
                                    FStar_List.map
                                      FStar_SMTEncoding_Util.mkFreeV vars in
                                  (tname, uu____14251) in
                                FStar_SMTEncoding_Util.mkApp uu____14247 in
                              let uu____14256 =
                                let tname_decl =
                                  let uu____14262 =
                                    let uu____14263 =
                                      FStar_All.pipe_right vars
                                        (FStar_List.map
                                           (fun uu____14278  ->
                                              match uu____14278 with
                                              | (n1,s) ->
                                                  ((Prims.strcat tname n1),
                                                    s, false))) in
                                    let uu____14286 = varops.next_id () in
                                    (tname, uu____14263,
                                      FStar_SMTEncoding_Term.Term_sort,
                                      uu____14286, false) in
                                  constructor_or_logic_type_decl uu____14262 in
                                let uu____14291 =
                                  match vars with
                                  | [] ->
                                      let uu____14298 =
                                        let uu____14299 =
                                          let uu____14301 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (tname, []) in
                                          FStar_All.pipe_left
                                            (fun _0_38  -> Some _0_38)
                                            uu____14301 in
                                        push_free_var env1 t tname
                                          uu____14299 in
                                      ([], uu____14298)
                                  | uu____14305 ->
                                      let ttok_decl =
                                        FStar_SMTEncoding_Term.DeclFun
                                          (ttok, [],
                                            FStar_SMTEncoding_Term.Term_sort,
                                            (Some "token")) in
                                      let ttok_fresh =
                                        let uu____14311 = varops.next_id () in
                                        FStar_SMTEncoding_Term.fresh_token
                                          (ttok,
                                            FStar_SMTEncoding_Term.Term_sort)
                                          uu____14311 in
                                      let ttok_app = mk_Apply ttok_tm vars in
                                      let pats = [[ttok_app]; [tapp]] in
                                      let name_tok_corr =
                                        let uu____14320 =
                                          let uu____14324 =
                                            let uu____14325 =
                                              let uu____14333 =
                                                FStar_SMTEncoding_Util.mkEq
                                                  (ttok_app, tapp) in
                                              (pats, None, vars, uu____14333) in
                                            FStar_SMTEncoding_Util.mkForall'
                                              uu____14325 in
                                          (uu____14324,
                                            (Some "name-token correspondence"),
                                            (Prims.strcat
                                               "token_correspondence_" ttok)) in
                                        FStar_SMTEncoding_Util.mkAssume
                                          uu____14320 in
                                      ([ttok_decl; ttok_fresh; name_tok_corr],
                                        env1) in
                                match uu____14291 with
                                | (tok_decls,env2) ->
                                    ((FStar_List.append tname_decl tok_decls),
                                      env2) in
                              (match uu____14256 with
                               | (decls,env2) ->
                                   let kindingAx =
                                     let uu____14356 =
                                       encode_term_pred None res1 env' tapp in
                                     match uu____14356 with
                                     | (k1,decls1) ->
                                         let karr =
                                           if
                                             (FStar_List.length formals1) >
                                               (Prims.parse_int "0")
                                           then
                                             let uu____14370 =
                                               let uu____14371 =
                                                 let uu____14375 =
                                                   let uu____14376 =
                                                     FStar_SMTEncoding_Term.mk_PreType
                                                       ttok_tm in
                                                   FStar_SMTEncoding_Term.mk_tester
                                                     "Tm_arrow" uu____14376 in
                                                 (uu____14375,
                                                   (Some "kinding"),
                                                   (Prims.strcat
                                                      "pre_kinding_" ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14371 in
                                             [uu____14370]
                                           else [] in
                                         let uu____14379 =
                                           let uu____14381 =
                                             let uu____14383 =
                                               let uu____14384 =
                                                 let uu____14388 =
                                                   let uu____14389 =
                                                     let uu____14395 =
                                                       FStar_SMTEncoding_Util.mkImp
                                                         (guard, k1) in
                                                     ([[tapp]], vars,
                                                       uu____14395) in
                                                   FStar_SMTEncoding_Util.mkForall
                                                     uu____14389 in
                                                 (uu____14388, None,
                                                   (Prims.strcat "kinding_"
                                                      ttok)) in
                                               FStar_SMTEncoding_Util.mkAssume
                                                 uu____14384 in
                                             [uu____14383] in
                                           FStar_List.append karr uu____14381 in
                                         FStar_List.append decls1 uu____14379 in
                                   let aux =
                                     let uu____14404 =
                                       let uu____14406 =
                                         inversion_axioms tapp vars in
                                       let uu____14408 =
                                         let uu____14410 =
                                           pretype_axiom env2 tapp vars in
                                         [uu____14410] in
                                       FStar_List.append uu____14406
                                         uu____14408 in
                                     FStar_List.append kindingAx uu____14404 in
                                   let g =
                                     FStar_List.append decls
                                       (FStar_List.append binder_decls aux) in
                                   (g, env2))))))
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14415,uu____14416,uu____14417,uu____14418,uu____14419)
          when FStar_Ident.lid_equals d FStar_Syntax_Const.lexcons_lid ->
          ([], env)
      | FStar_Syntax_Syntax.Sig_datacon
          (d,uu____14424,t,uu____14426,n_tps,uu____14428) ->
          let quals = se.FStar_Syntax_Syntax.sigquals in
          let uu____14433 = new_term_constant_and_tok_from_lid env d in
          (match uu____14433 with
           | (ddconstrsym,ddtok,env1) ->
               let ddtok_tm = FStar_SMTEncoding_Util.mkApp (ddtok, []) in
               let uu____14444 = FStar_Syntax_Util.arrow_formals t in
               (match uu____14444 with
                | (formals,t_res) ->
                    let uu____14466 =
                      fresh_fvar "f" FStar_SMTEncoding_Term.Fuel_sort in
                    (match uu____14466 with
                     | (fuel_var,fuel_tm) ->
                         let s_fuel_tm =
                           FStar_SMTEncoding_Util.mkApp ("SFuel", [fuel_tm]) in
                         let uu____14475 =
                           encode_binders (Some fuel_tm) formals env1 in
                         (match uu____14475 with
                          | (vars,guards,env',binder_decls,names1) ->
                              let fields =
                                FStar_All.pipe_right names1
                                  (FStar_List.mapi
                                     (fun n1  ->
                                        fun x  ->
                                          let projectible = true in
                                          let uu____14513 =
                                            mk_term_projector_name d x in
                                          (uu____14513,
                                            FStar_SMTEncoding_Term.Term_sort,
                                            projectible))) in
                              let datacons =
                                let uu____14515 =
                                  let uu____14525 = varops.next_id () in
                                  (ddconstrsym, fields,
                                    FStar_SMTEncoding_Term.Term_sort,
                                    uu____14525, true) in
                                FStar_All.pipe_right uu____14515
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
                              let uu____14547 =
                                encode_term_pred None t env1 ddtok_tm in
                              (match uu____14547 with
                               | (tok_typing,decls3) ->
                                   let tok_typing1 =
                                     match fields with
                                     | uu____14555::uu____14556 ->
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
                                         let uu____14581 =
                                           let uu____14587 =
                                             FStar_SMTEncoding_Term.mk_NoHoist
                                               f tok_typing in
                                           ([[vtok_app_l]; [vtok_app_r]],
                                             [ff], uu____14587) in
                                         FStar_SMTEncoding_Util.mkForall
                                           uu____14581
                                     | uu____14600 -> tok_typing in
                                   let uu____14605 =
                                     encode_binders (Some fuel_tm) formals
                                       env1 in
                                   (match uu____14605 with
                                    | (vars',guards',env'',decls_formals,uu____14620)
                                        ->
                                        let uu____14627 =
                                          let xvars1 =
                                            FStar_List.map
                                              FStar_SMTEncoding_Util.mkFreeV
                                              vars' in
                                          let dapp1 =
                                            FStar_SMTEncoding_Util.mkApp
                                              (ddconstrsym, xvars1) in
                                          encode_term_pred (Some fuel_tm)
                                            t_res env'' dapp1 in
                                        (match uu____14627 with
                                         | (ty_pred',decls_pred) ->
                                             let guard' =
                                               FStar_SMTEncoding_Util.mk_and_l
                                                 guards' in
                                             let proxy_fresh =
                                               match formals with
                                               | [] -> []
                                               | uu____14646 ->
                                                   let uu____14650 =
                                                     let uu____14651 =
                                                       varops.next_id () in
                                                     FStar_SMTEncoding_Term.fresh_token
                                                       (ddtok,
                                                         FStar_SMTEncoding_Term.Term_sort)
                                                       uu____14651 in
                                                   [uu____14650] in
                                             let encode_elim uu____14658 =
                                               let uu____14659 =
                                                 FStar_Syntax_Util.head_and_args
                                                   t_res in
                                               match uu____14659 with
                                               | (head1,args) ->
                                                   let uu____14688 =
                                                     let uu____14689 =
                                                       FStar_Syntax_Subst.compress
                                                         head1 in
                                                     uu____14689.FStar_Syntax_Syntax.n in
                                                   (match uu____14688 with
                                                    | FStar_Syntax_Syntax.Tm_uinst
                                                        ({
                                                           FStar_Syntax_Syntax.n
                                                             =
                                                             FStar_Syntax_Syntax.Tm_fvar
                                                             fv;
                                                           FStar_Syntax_Syntax.tk
                                                             = uu____14696;
                                                           FStar_Syntax_Syntax.pos
                                                             = uu____14697;
                                                           FStar_Syntax_Syntax.vars
                                                             = uu____14698;_},uu____14699)
                                                        ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14709 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14709
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
                                                                 | uu____14735
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____14743
                                                                    =
                                                                    let uu____14744
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____14744 in
                                                                    if
                                                                    uu____14743
                                                                    then
                                                                    let uu____14751
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____14751]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____14753
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____14766
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____14766
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____14788
                                                                    =
                                                                    let uu____14792
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____14792 in
                                                                    (match uu____14788
                                                                    with
                                                                    | 
                                                                    (uu____14799,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____14805
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____14805
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____14807
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____14807
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
                                                             (match uu____14753
                                                              with
                                                              | (uu____14815,arg_vars,elim_eqns_or_guards,uu____14818)
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
                                                                    let uu____14837
                                                                    =
                                                                    let uu____14841
                                                                    =
                                                                    let uu____14842
                                                                    =
                                                                    let uu____14848
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14854
                                                                    =
                                                                    let uu____14855
                                                                    =
                                                                    let uu____14858
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____14858) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14855 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14848,
                                                                    uu____14854) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14842 in
                                                                    (uu____14841,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14837 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____14871
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____14871,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____14873
                                                                    =
                                                                    let uu____14877
                                                                    =
                                                                    let uu____14878
                                                                    =
                                                                    let uu____14884
                                                                    =
                                                                    let uu____14887
                                                                    =
                                                                    let uu____14889
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____14889] in
                                                                    [uu____14887] in
                                                                    let uu____14892
                                                                    =
                                                                    let uu____14893
                                                                    =
                                                                    let uu____14896
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____14897
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____14896,
                                                                    uu____14897) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14893 in
                                                                    (uu____14884,
                                                                    [x],
                                                                    uu____14892) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14878 in
                                                                    let uu____14907
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____14877,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____14907) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14873
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____14912
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
                                                                    (let uu____14927
                                                                    =
                                                                    let uu____14928
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____14928
                                                                    dapp1 in
                                                                    [uu____14927]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____14912
                                                                    FStar_List.flatten in
                                                                    let uu____14932
                                                                    =
                                                                    let uu____14936
                                                                    =
                                                                    let uu____14937
                                                                    =
                                                                    let uu____14943
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____14949
                                                                    =
                                                                    let uu____14950
                                                                    =
                                                                    let uu____14953
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____14953) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____14950 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____14943,
                                                                    uu____14949) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____14937 in
                                                                    (uu____14936,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____14932) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | FStar_Syntax_Syntax.Tm_fvar
                                                        fv ->
                                                        let encoded_head =
                                                          lookup_free_var_name
                                                            env'
                                                            fv.FStar_Syntax_Syntax.fv_name in
                                                        let uu____14969 =
                                                          encode_args args
                                                            env' in
                                                        (match uu____14969
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
                                                                 | uu____14995
                                                                    ->
                                                                    failwith
                                                                    "Impossible: parameter must be a variable" in
                                                               let guards1 =
                                                                 FStar_All.pipe_right
                                                                   guards
                                                                   (FStar_List.collect
                                                                    (fun g 
                                                                    ->
                                                                    let uu____15003
                                                                    =
                                                                    let uu____15004
                                                                    =
                                                                    FStar_SMTEncoding_Term.free_variables
                                                                    g in
                                                                    FStar_List.contains
                                                                    fv1
                                                                    uu____15004 in
                                                                    if
                                                                    uu____15003
                                                                    then
                                                                    let uu____15011
                                                                    =
                                                                    FStar_SMTEncoding_Term.subst
                                                                    g fv1 xv in
                                                                    [uu____15011]
                                                                    else [])) in
                                                               FStar_SMTEncoding_Util.mk_and_l
                                                                 guards1 in
                                                             let uu____15013
                                                               =
                                                               FStar_List.fold_left
                                                                 (fun
                                                                    uu____15026
                                                                     ->
                                                                    fun arg 
                                                                    ->
                                                                    match uu____15026
                                                                    with
                                                                    | 
                                                                    (env2,arg_vars,eqns_or_guards,i)
                                                                    ->
                                                                    let uu____15048
                                                                    =
                                                                    let uu____15052
                                                                    =
                                                                    FStar_Syntax_Syntax.new_bv
                                                                    None
                                                                    FStar_Syntax_Syntax.tun in
                                                                    gen_term_var
                                                                    env2
                                                                    uu____15052 in
                                                                    (match uu____15048
                                                                    with
                                                                    | 
                                                                    (uu____15059,xv,env3)
                                                                    ->
                                                                    let eqns
                                                                    =
                                                                    if
                                                                    i < n_tps
                                                                    then
                                                                    let uu____15065
                                                                    =
                                                                    guards_for_parameter
                                                                    arg xv in
                                                                    uu____15065
                                                                    ::
                                                                    eqns_or_guards
                                                                    else
                                                                    (let uu____15067
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (arg, xv) in
                                                                    uu____15067
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
                                                             (match uu____15013
                                                              with
                                                              | (uu____15075,arg_vars,elim_eqns_or_guards,uu____15078)
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
                                                                    let uu____15097
                                                                    =
                                                                    let uu____15101
                                                                    =
                                                                    let uu____15102
                                                                    =
                                                                    let uu____15108
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15114
                                                                    =
                                                                    let uu____15115
                                                                    =
                                                                    let uu____15118
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    (FStar_List.append
                                                                    elim_eqns_or_guards
                                                                    guards) in
                                                                    (ty_pred,
                                                                    uu____15118) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15115 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15108,
                                                                    uu____15114) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15102 in
                                                                    (uu____15101,
                                                                    (Some
                                                                    "data constructor typing elim"),
                                                                    (Prims.strcat
                                                                    "data_elim_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15097 in
                                                                  let subterm_ordering
                                                                    =
                                                                    if
                                                                    FStar_Ident.lid_equals
                                                                    d
                                                                    FStar_Syntax_Const.lextop_lid
                                                                    then
                                                                    let x =
                                                                    let uu____15131
                                                                    =
                                                                    varops.fresh
                                                                    "x" in
                                                                    (uu____15131,
                                                                    FStar_SMTEncoding_Term.Term_sort) in
                                                                    let xtm =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    x in
                                                                    let uu____15133
                                                                    =
                                                                    let uu____15137
                                                                    =
                                                                    let uu____15138
                                                                    =
                                                                    let uu____15144
                                                                    =
                                                                    let uu____15147
                                                                    =
                                                                    let uu____15149
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    [uu____15149] in
                                                                    [uu____15147] in
                                                                    let uu____15152
                                                                    =
                                                                    let uu____15153
                                                                    =
                                                                    let uu____15156
                                                                    =
                                                                    FStar_SMTEncoding_Term.mk_tester
                                                                    "LexCons"
                                                                    xtm in
                                                                    let uu____15157
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    xtm dapp1 in
                                                                    (uu____15156,
                                                                    uu____15157) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15153 in
                                                                    (uu____15144,
                                                                    [x],
                                                                    uu____15152) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15138 in
                                                                    let uu____15167
                                                                    =
                                                                    varops.mk_unique
                                                                    "lextop" in
                                                                    (uu____15137,
                                                                    (Some
                                                                    "lextop is top"),
                                                                    uu____15167) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15133
                                                                    else
                                                                    (let prec
                                                                    =
                                                                    let uu____15172
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
                                                                    (let uu____15187
                                                                    =
                                                                    let uu____15188
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkFreeV
                                                                    v1 in
                                                                    FStar_SMTEncoding_Util.mk_Precedes
                                                                    uu____15188
                                                                    dapp1 in
                                                                    [uu____15187]))) in
                                                                    FStar_All.pipe_right
                                                                    uu____15172
                                                                    FStar_List.flatten in
                                                                    let uu____15192
                                                                    =
                                                                    let uu____15196
                                                                    =
                                                                    let uu____15197
                                                                    =
                                                                    let uu____15203
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    (FStar_List.append
                                                                    vars
                                                                    arg_binders) in
                                                                    let uu____15209
                                                                    =
                                                                    let uu____15210
                                                                    =
                                                                    let uu____15213
                                                                    =
                                                                    FStar_SMTEncoding_Util.mk_and_l
                                                                    prec in
                                                                    (ty_pred,
                                                                    uu____15213) in
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    uu____15210 in
                                                                    ([
                                                                    [ty_pred]],
                                                                    uu____15203,
                                                                    uu____15209) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15197 in
                                                                    (uu____15196,
                                                                    (Some
                                                                    "subterm ordering"),
                                                                    (Prims.strcat
                                                                    "subterm_ordering_"
                                                                    ddconstrsym)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15192) in
                                                                  (arg_decls,
                                                                    [typing_inversion;
                                                                    subterm_ordering])))
                                                    | uu____15223 ->
                                                        ((let uu____15225 =
                                                            let uu____15226 =
                                                              FStar_Syntax_Print.lid_to_string
                                                                d in
                                                            let uu____15227 =
                                                              FStar_Syntax_Print.term_to_string
                                                                head1 in
                                                            FStar_Util.format2
                                                              "Constructor %s builds an unexpected type %s\n"
                                                              uu____15226
                                                              uu____15227 in
                                                          FStar_Errors.warn
                                                            se.FStar_Syntax_Syntax.sigrng
                                                            uu____15225);
                                                         ([], []))) in
                                             let uu____15230 = encode_elim () in
                                             (match uu____15230 with
                                              | (decls2,elim) ->
                                                  let g =
                                                    let uu____15242 =
                                                      let uu____15244 =
                                                        let uu____15246 =
                                                          let uu____15248 =
                                                            let uu____15250 =
                                                              let uu____15251
                                                                =
                                                                let uu____15257
                                                                  =
                                                                  let uu____15259
                                                                    =
                                                                    let uu____15260
                                                                    =
                                                                    FStar_Syntax_Print.lid_to_string
                                                                    d in
                                                                    FStar_Util.format1
                                                                    "data constructor proxy: %s"
                                                                    uu____15260 in
                                                                  Some
                                                                    uu____15259 in
                                                                (ddtok, [],
                                                                  FStar_SMTEncoding_Term.Term_sort,
                                                                  uu____15257) in
                                                              FStar_SMTEncoding_Term.DeclFun
                                                                uu____15251 in
                                                            [uu____15250] in
                                                          let uu____15263 =
                                                            let uu____15265 =
                                                              let uu____15267
                                                                =
                                                                let uu____15269
                                                                  =
                                                                  let uu____15271
                                                                    =
                                                                    let uu____15273
                                                                    =
                                                                    let uu____15275
                                                                    =
                                                                    let uu____15276
                                                                    =
                                                                    let uu____15280
                                                                    =
                                                                    let uu____15281
                                                                    =
                                                                    let uu____15287
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkEq
                                                                    (app,
                                                                    dapp) in
                                                                    ([[app]],
                                                                    vars,
                                                                    uu____15287) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15281 in
                                                                    (uu____15280,
                                                                    (Some
                                                                    "equality for proxy"),
                                                                    (Prims.strcat
                                                                    "equality_tok_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15276 in
                                                                    let uu____15294
                                                                    =
                                                                    let uu____15296
                                                                    =
                                                                    let uu____15297
                                                                    =
                                                                    let uu____15301
                                                                    =
                                                                    let uu____15302
                                                                    =
                                                                    let uu____15308
                                                                    =
                                                                    add_fuel
                                                                    (fuel_var,
                                                                    FStar_SMTEncoding_Term.Fuel_sort)
                                                                    vars' in
                                                                    let uu____15314
                                                                    =
                                                                    FStar_SMTEncoding_Util.mkImp
                                                                    (guard',
                                                                    ty_pred') in
                                                                    ([
                                                                    [ty_pred']],
                                                                    uu____15308,
                                                                    uu____15314) in
                                                                    FStar_SMTEncoding_Util.mkForall
                                                                    uu____15302 in
                                                                    (uu____15301,
                                                                    (Some
                                                                    "data constructor typing intro"),
                                                                    (Prims.strcat
                                                                    "data_typing_intro_"
                                                                    ddtok)) in
                                                                    FStar_SMTEncoding_Util.mkAssume
                                                                    uu____15297 in
                                                                    [uu____15296] in
                                                                    uu____15275
                                                                    ::
                                                                    uu____15294 in
                                                                    (FStar_SMTEncoding_Util.mkAssume
                                                                    (tok_typing1,
                                                                    (Some
                                                                    "typing for data constructor proxy"),
                                                                    (Prims.strcat
                                                                    "typing_tok_"
                                                                    ddtok)))
                                                                    ::
                                                                    uu____15273 in
                                                                  FStar_List.append
                                                                    uu____15271
                                                                    elim in
                                                                FStar_List.append
                                                                  decls_pred
                                                                  uu____15269 in
                                                              FStar_List.append
                                                                decls_formals
                                                                uu____15267 in
                                                            FStar_List.append
                                                              proxy_fresh
                                                              uu____15265 in
                                                          FStar_List.append
                                                            uu____15248
                                                            uu____15263 in
                                                        FStar_List.append
                                                          decls3 uu____15246 in
                                                      FStar_List.append
                                                        decls2 uu____15244 in
                                                    FStar_List.append
                                                      binder_decls
                                                      uu____15242 in
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
           (fun uu____15335  ->
              fun se  ->
                match uu____15335 with
                | (g,env1) ->
                    let uu____15347 = encode_sigelt env1 se in
                    (match uu____15347 with
                     | (g',env2) -> ((FStar_List.append g g'), env2)))
           ([], env))
let encode_env_bindings:
  env_t ->
    FStar_TypeChecker_Env.binding Prims.list ->
      (FStar_SMTEncoding_Term.decls_t* env_t)
  =
  fun env  ->
    fun bindings  ->
      let encode_binding b uu____15383 =
        match uu____15383 with
        | (i,decls,env1) ->
            (match b with
             | FStar_TypeChecker_Env.Binding_univ uu____15401 ->
                 ((i + (Prims.parse_int "1")), [], env1)
             | FStar_TypeChecker_Env.Binding_var x ->
                 let t1 =
                   FStar_TypeChecker_Normalize.normalize
                     [FStar_TypeChecker_Normalize.Beta;
                     FStar_TypeChecker_Normalize.Eager_unfolding;
                     FStar_TypeChecker_Normalize.Simplify;
                     FStar_TypeChecker_Normalize.EraseUniverses] env1.tcenv
                     x.FStar_Syntax_Syntax.sort in
                 ((let uu____15406 =
                     FStar_All.pipe_left
                       (FStar_TypeChecker_Env.debug env1.tcenv)
                       (FStar_Options.Other "SMTEncoding") in
                   if uu____15406
                   then
                     let uu____15407 = FStar_Syntax_Print.bv_to_string x in
                     let uu____15408 =
                       FStar_Syntax_Print.term_to_string
                         x.FStar_Syntax_Syntax.sort in
                     let uu____15409 = FStar_Syntax_Print.term_to_string t1 in
                     FStar_Util.print3 "Normalized %s : %s to %s\n"
                       uu____15407 uu____15408 uu____15409
                   else ());
                  (let uu____15411 = encode_term t1 env1 in
                   match uu____15411 with
                   | (t,decls') ->
                       let t_hash = FStar_SMTEncoding_Term.hash_of_term t in
                       let uu____15421 =
                         let uu____15425 =
                           let uu____15426 =
                             let uu____15427 =
                               FStar_Util.digest_of_string t_hash in
                             Prims.strcat uu____15427
                               (Prims.strcat "_" (Prims.string_of_int i)) in
                           Prims.strcat "x_" uu____15426 in
                         new_term_constant_from_string env1 x uu____15425 in
                       (match uu____15421 with
                        | (xxsym,xx,env') ->
                            let t2 =
                              FStar_SMTEncoding_Term.mk_HasTypeWithFuel None
                                xx t in
                            let caption =
                              let uu____15438 = FStar_Options.log_queries () in
                              if uu____15438
                              then
                                let uu____15440 =
                                  let uu____15441 =
                                    FStar_Syntax_Print.bv_to_string x in
                                  let uu____15442 =
                                    FStar_Syntax_Print.term_to_string
                                      x.FStar_Syntax_Syntax.sort in
                                  let uu____15443 =
                                    FStar_Syntax_Print.term_to_string t1 in
                                  FStar_Util.format3 "%s : %s (%s)"
                                    uu____15441 uu____15442 uu____15443 in
                                Some uu____15440
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
             | FStar_TypeChecker_Env.Binding_lid (x,(uu____15454,t)) ->
                 let t_norm = whnf env1 t in
                 let fv =
                   FStar_Syntax_Syntax.lid_as_fv x
                     FStar_Syntax_Syntax.Delta_constant None in
                 let uu____15463 = encode_free_var env1 fv t t_norm [] in
                 (match uu____15463 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig_inst
                 (uu____15476,se,uu____15478) ->
                 let uu____15481 = encode_sigelt env1 se in
                 (match uu____15481 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))
             | FStar_TypeChecker_Env.Binding_sig (uu____15491,se) ->
                 let uu____15495 = encode_sigelt env1 se in
                 (match uu____15495 with
                  | (g,env') ->
                      ((i + (Prims.parse_int "1")),
                        (FStar_List.append decls g), env'))) in
      let uu____15505 =
        FStar_List.fold_right encode_binding bindings
          ((Prims.parse_int "0"), [], env) in
      match uu____15505 with | (uu____15517,decls,env1) -> (decls, env1)
let encode_labels labs =
  let prefix1 =
    FStar_All.pipe_right labs
      (FStar_List.map
         (fun uu____15562  ->
            match uu____15562 with
            | (l,uu____15569,uu____15570) ->
                FStar_SMTEncoding_Term.DeclFun
                  ((fst l), [], FStar_SMTEncoding_Term.Bool_sort, None))) in
  let suffix =
    FStar_All.pipe_right labs
      (FStar_List.collect
         (fun uu____15591  ->
            match uu____15591 with
            | (l,uu____15599,uu____15600) ->
                let uu____15605 =
                  FStar_All.pipe_left
                    (fun _0_39  -> FStar_SMTEncoding_Term.Echo _0_39) (
                    fst l) in
                let uu____15606 =
                  let uu____15608 =
                    let uu____15609 = FStar_SMTEncoding_Util.mkFreeV l in
                    FStar_SMTEncoding_Term.Eval uu____15609 in
                  [uu____15608] in
                uu____15605 :: uu____15606)) in
  (prefix1, suffix)
let last_env: env_t Prims.list FStar_ST.ref = FStar_Util.mk_ref []
let init_env: FStar_TypeChecker_Env.env -> Prims.unit =
  fun tcenv  ->
    let uu____15620 =
      let uu____15622 =
        let uu____15623 = FStar_Util.smap_create (Prims.parse_int "100") in
        let uu____15625 =
          let uu____15626 = FStar_TypeChecker_Env.current_module tcenv in
          FStar_All.pipe_right uu____15626 FStar_Ident.string_of_lid in
        {
          bindings = [];
          depth = (Prims.parse_int "0");
          tcenv;
          warn = true;
          cache = uu____15623;
          nolabels = false;
          use_zfuel_name = false;
          encode_non_total_function_typ = true;
          current_module_name = uu____15625
        } in
      [uu____15622] in
    FStar_ST.write last_env uu____15620
let get_env: FStar_Ident.lident -> FStar_TypeChecker_Env.env -> env_t =
  fun cmn  ->
    fun tcenv  ->
      let uu____15636 = FStar_ST.read last_env in
      match uu____15636 with
      | [] -> failwith "No env; call init first!"
      | e::uu____15642 ->
          let uu___154_15644 = e in
          let uu____15645 = FStar_Ident.string_of_lid cmn in
          {
            bindings = (uu___154_15644.bindings);
            depth = (uu___154_15644.depth);
            tcenv;
            warn = (uu___154_15644.warn);
            cache = (uu___154_15644.cache);
            nolabels = (uu___154_15644.nolabels);
            use_zfuel_name = (uu___154_15644.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___154_15644.encode_non_total_function_typ);
            current_module_name = uu____15645
          }
let set_env: env_t -> Prims.unit =
  fun env  ->
    let uu____15649 = FStar_ST.read last_env in
    match uu____15649 with
    | [] -> failwith "Empty env stack"
    | uu____15654::tl1 -> FStar_ST.write last_env (env :: tl1)
let push_env: Prims.unit -> Prims.unit =
  fun uu____15662  ->
    let uu____15663 = FStar_ST.read last_env in
    match uu____15663 with
    | [] -> failwith "Empty env stack"
    | hd1::tl1 ->
        let refs = FStar_Util.smap_copy hd1.cache in
        let top =
          let uu___155_15674 = hd1 in
          {
            bindings = (uu___155_15674.bindings);
            depth = (uu___155_15674.depth);
            tcenv = (uu___155_15674.tcenv);
            warn = (uu___155_15674.warn);
            cache = refs;
            nolabels = (uu___155_15674.nolabels);
            use_zfuel_name = (uu___155_15674.use_zfuel_name);
            encode_non_total_function_typ =
              (uu___155_15674.encode_non_total_function_typ);
            current_module_name = (uu___155_15674.current_module_name)
          } in
        FStar_ST.write last_env (top :: hd1 :: tl1)
let pop_env: Prims.unit -> Prims.unit =
  fun uu____15680  ->
    let uu____15681 = FStar_ST.read last_env in
    match uu____15681 with
    | [] -> failwith "Popping an empty stack"
    | uu____15686::tl1 -> FStar_ST.write last_env tl1
let mark_env: Prims.unit -> Prims.unit = fun uu____15694  -> push_env ()
let reset_mark_env: Prims.unit -> Prims.unit = fun uu____15697  -> pop_env ()
let commit_mark_env: Prims.unit -> Prims.unit =
  fun uu____15700  ->
    let uu____15701 = FStar_ST.read last_env in
    match uu____15701 with
    | hd1::uu____15707::tl1 -> FStar_ST.write last_env (hd1 :: tl1)
    | uu____15713 -> failwith "Impossible"
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
        | (uu____15762::uu____15763,FStar_SMTEncoding_Term.Assume a) ->
            FStar_SMTEncoding_Term.Assume
              (let uu___156_15767 = a in
               {
                 FStar_SMTEncoding_Term.assumption_term =
                   (uu___156_15767.FStar_SMTEncoding_Term.assumption_term);
                 FStar_SMTEncoding_Term.assumption_caption =
                   (uu___156_15767.FStar_SMTEncoding_Term.assumption_caption);
                 FStar_SMTEncoding_Term.assumption_name =
                   (uu___156_15767.FStar_SMTEncoding_Term.assumption_name);
                 FStar_SMTEncoding_Term.assumption_fact_ids = fact_db_ids
               })
        | uu____15768 -> d
let fact_dbs_for_lid:
  env_t -> FStar_Ident.lid -> FStar_SMTEncoding_Term.fact_db_id Prims.list =
  fun env  ->
    fun lid  ->
      let uu____15779 =
        let uu____15781 =
          let uu____15782 = FStar_Ident.lid_of_ids lid.FStar_Ident.ns in
          FStar_SMTEncoding_Term.Namespace uu____15782 in
        let uu____15783 = open_fact_db_tags env in uu____15781 :: uu____15783 in
      (FStar_SMTEncoding_Term.Name lid) :: uu____15779
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
      let uu____15798 = encode_sigelt env se in
      match uu____15798 with
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
        let uu____15823 = FStar_Options.log_queries () in
        if uu____15823
        then
          let uu____15825 =
            let uu____15826 =
              let uu____15827 =
                let uu____15828 =
                  FStar_All.pipe_right (FStar_Syntax_Util.lids_of_sigelt se)
                    (FStar_List.map FStar_Syntax_Print.lid_to_string) in
                FStar_All.pipe_right uu____15828 (FStar_String.concat ", ") in
              Prims.strcat "encoding sigelt " uu____15827 in
            FStar_SMTEncoding_Term.Caption uu____15826 in
          uu____15825 :: decls
        else decls in
      let env =
        let uu____15835 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____15835 tcenv in
      let uu____15836 = encode_top_level_facts env se in
      match uu____15836 with
      | (decls,env1) ->
          (set_env env1;
           (let uu____15845 = caption decls in
            FStar_SMTEncoding_Z3.giveZ3 uu____15845))
let encode_modul:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.modul -> Prims.unit =
  fun tcenv  ->
    fun modul  ->
      let name =
        FStar_Util.format2 "%s %s"
          (if modul.FStar_Syntax_Syntax.is_interface
           then "interface"
           else "module") (modul.FStar_Syntax_Syntax.name).FStar_Ident.str in
      (let uu____15856 = FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
       if uu____15856
       then
         let uu____15857 =
           FStar_All.pipe_right
             (FStar_List.length modul.FStar_Syntax_Syntax.exports)
             Prims.string_of_int in
         FStar_Util.print2
           "+++++++++++Encoding externals for %s ... %s exports\n" name
           uu____15857
       else ());
      (let env = get_env modul.FStar_Syntax_Syntax.name tcenv in
       let encode_signature env1 ses =
         FStar_All.pipe_right ses
           (FStar_List.fold_left
              (fun uu____15878  ->
                 fun se  ->
                   match uu____15878 with
                   | (g,env2) ->
                       let uu____15890 = encode_top_level_facts env2 se in
                       (match uu____15890 with
                        | (g',env3) -> ((FStar_List.append g g'), env3)))
              ([], env1)) in
       let uu____15903 =
         encode_signature
           (let uu___157_15907 = env in
            {
              bindings = (uu___157_15907.bindings);
              depth = (uu___157_15907.depth);
              tcenv = (uu___157_15907.tcenv);
              warn = false;
              cache = (uu___157_15907.cache);
              nolabels = (uu___157_15907.nolabels);
              use_zfuel_name = (uu___157_15907.use_zfuel_name);
              encode_non_total_function_typ =
                (uu___157_15907.encode_non_total_function_typ);
              current_module_name = (uu___157_15907.current_module_name)
            }) modul.FStar_Syntax_Syntax.exports in
       match uu____15903 with
       | (decls,env1) ->
           let caption decls1 =
             let uu____15919 = FStar_Options.log_queries () in
             if uu____15919
             then
               let msg = Prims.strcat "Externals for " name in
               FStar_List.append ((FStar_SMTEncoding_Term.Caption msg) ::
                 decls1)
                 [FStar_SMTEncoding_Term.Caption (Prims.strcat "End " msg)]
             else decls1 in
           (set_env
              (let uu___158_15924 = env1 in
               {
                 bindings = (uu___158_15924.bindings);
                 depth = (uu___158_15924.depth);
                 tcenv = (uu___158_15924.tcenv);
                 warn = true;
                 cache = (uu___158_15924.cache);
                 nolabels = (uu___158_15924.nolabels);
                 use_zfuel_name = (uu___158_15924.use_zfuel_name);
                 encode_non_total_function_typ =
                   (uu___158_15924.encode_non_total_function_typ);
                 current_module_name = (uu___158_15924.current_module_name)
               });
            (let uu____15926 =
               FStar_TypeChecker_Env.debug tcenv FStar_Options.Low in
             if uu____15926
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
        (let uu____15961 =
           let uu____15962 = FStar_TypeChecker_Env.current_module tcenv in
           uu____15962.FStar_Ident.str in
         FStar_SMTEncoding_Z3.query_logging.FStar_SMTEncoding_Z3.set_module_name
           uu____15961);
        (let env =
           let uu____15964 = FStar_TypeChecker_Env.current_module tcenv in
           get_env uu____15964 tcenv in
         let bindings =
           FStar_TypeChecker_Env.fold_env tcenv
             (fun bs  -> fun b  -> b :: bs) [] in
         let uu____15971 =
           let rec aux bindings1 =
             match bindings1 with
             | (FStar_TypeChecker_Env.Binding_var x)::rest ->
                 let uu____15992 = aux rest in
                 (match uu____15992 with
                  | (out,rest1) ->
                      let t =
                        let uu____16010 =
                          FStar_Syntax_Util.destruct_typ_as_formula
                            x.FStar_Syntax_Syntax.sort in
                        match uu____16010 with
                        | Some uu____16014 ->
                            let uu____16015 =
                              FStar_Syntax_Syntax.new_bv None
                                FStar_TypeChecker_Common.t_unit in
                            FStar_Syntax_Util.refine uu____16015
                              x.FStar_Syntax_Syntax.sort
                        | uu____16016 -> x.FStar_Syntax_Syntax.sort in
                      let t1 =
                        FStar_TypeChecker_Normalize.normalize
                          [FStar_TypeChecker_Normalize.Eager_unfolding;
                          FStar_TypeChecker_Normalize.Beta;
                          FStar_TypeChecker_Normalize.Simplify;
                          FStar_TypeChecker_Normalize.EraseUniverses]
                          env.tcenv t in
                      let uu____16019 =
                        let uu____16021 =
                          FStar_Syntax_Syntax.mk_binder
                            (let uu___159_16022 = x in
                             {
                               FStar_Syntax_Syntax.ppname =
                                 (uu___159_16022.FStar_Syntax_Syntax.ppname);
                               FStar_Syntax_Syntax.index =
                                 (uu___159_16022.FStar_Syntax_Syntax.index);
                               FStar_Syntax_Syntax.sort = t1
                             }) in
                        uu____16021 :: out in
                      (uu____16019, rest1))
             | uu____16025 -> ([], bindings1) in
           let uu____16029 = aux bindings in
           match uu____16029 with
           | (closing,bindings1) ->
               let uu____16043 =
                 FStar_Syntax_Util.close_forall_no_univs
                   (FStar_List.rev closing) q in
               (uu____16043, bindings1) in
         match uu____15971 with
         | (q1,bindings1) ->
             let uu____16056 =
               let uu____16059 =
                 FStar_List.filter
                   (fun uu___125_16061  ->
                      match uu___125_16061 with
                      | FStar_TypeChecker_Env.Binding_sig uu____16062 ->
                          false
                      | uu____16066 -> true) bindings1 in
               encode_env_bindings env uu____16059 in
             (match uu____16056 with
              | (env_decls,env1) ->
                  ((let uu____16077 =
                      ((FStar_TypeChecker_Env.debug tcenv FStar_Options.Low)
                         ||
                         (FStar_All.pipe_left
                            (FStar_TypeChecker_Env.debug tcenv)
                            (FStar_Options.Other "SMTEncoding")))
                        ||
                        (FStar_All.pipe_left
                           (FStar_TypeChecker_Env.debug tcenv)
                           (FStar_Options.Other "SMTQuery")) in
                    if uu____16077
                    then
                      let uu____16078 = FStar_Syntax_Print.term_to_string q1 in
                      FStar_Util.print1 "Encoding query formula: %s\n"
                        uu____16078
                    else ());
                   (let uu____16080 = encode_formula q1 env1 in
                    match uu____16080 with
                    | (phi,qdecls) ->
                        let uu____16092 =
                          let uu____16095 =
                            FStar_TypeChecker_Env.get_range tcenv in
                          FStar_SMTEncoding_ErrorReporting.label_goals
                            use_env_msg uu____16095 phi in
                        (match uu____16092 with
                         | (labels,phi1) ->
                             let uu____16105 = encode_labels labels in
                             (match uu____16105 with
                              | (label_prefix,label_suffix) ->
                                  let query_prelude =
                                    FStar_List.append env_decls
                                      (FStar_List.append label_prefix qdecls) in
                                  let qry =
                                    let uu____16126 =
                                      let uu____16130 =
                                        FStar_SMTEncoding_Util.mkNot phi1 in
                                      let uu____16131 =
                                        varops.mk_unique "@query" in
                                      (uu____16130, (Some "query"),
                                        uu____16131) in
                                    FStar_SMTEncoding_Util.mkAssume
                                      uu____16126 in
                                  let suffix =
                                    FStar_List.append label_suffix
                                      [FStar_SMTEncoding_Term.Echo "Done!"] in
                                  (query_prelude, labels, qry, suffix)))))))
let is_trivial:
  FStar_TypeChecker_Env.env -> FStar_Syntax_Syntax.typ -> Prims.bool =
  fun tcenv  ->
    fun q  ->
      let env =
        let uu____16144 = FStar_TypeChecker_Env.current_module tcenv in
        get_env uu____16144 tcenv in
      FStar_SMTEncoding_Z3.push "query";
      (let uu____16146 = encode_formula q env in
       match uu____16146 with
       | (f,uu____16150) ->
           (FStar_SMTEncoding_Z3.pop "query";
            (match f.FStar_SMTEncoding_Term.tm with
             | FStar_SMTEncoding_Term.App
                 (FStar_SMTEncoding_Term.TrueOp ,uu____16152) -> true
             | uu____16155 -> false)))